import com.sun.source.tree.MethodTree;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Position;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.ext.RequiresClause;

import javax.lang.model.element.Modifier;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static com.sun.tools.javac.tree.JCTree.*;
import static org.jmlspecs.openjml.JmlTree.*;

/**
 * Created by jklamroth on 11/13/18.
 *
 * This Visitor translates methods and their translation into Java!?
 */
public class VerifyFunctionVisitor extends FilterVisitor {
    private final Maker M;
    private final Context context;
    private final Symtab syms;
    private final JmlTreeUtils treeutils;
    private final TranslationUtils transUtils;
    private final ClassReader reader;
    private Set<JCExpression> ensuresList = new HashSet<>();
    private Set<JCExpression> requiresList = new HashSet<>();
    protected JmlMethodDecl currentMethod;
    private List<JCStatement> newStatements = List.nil();
    private List<JCStatement> combinedNewReqStatements = List.nil();
    private List<JCStatement> combinedNewEnsStatements = List.nil();
    private Symbol returnVar = null;
    private boolean hasReturn = false;
    private VerifyFunctionVisitor.TranslationMode translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
    private Map<JCExpression, JCVariableDecl> oldVars = new HashMap<>();
    private  final BaseVisitor baseVisitor;
    private List<JCExpression> currentAssignable = null;

    public enum TranslationMode {ASSUME, ASSERT, JAVA, DEMONIC}

    public VerifyFunctionVisitor(Context context, Maker maker, BaseVisitor base) {
        super(context, maker);
        baseVisitor = base;
        this.context = context;
        this.M = Maker.instance(context);
        this.syms = Symtab.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.transUtils = new TranslationUtils(context, M);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
    }

    @Override
    public JCTree visitJmlMethodClauseExpr(JmlMethodClauseExpr that, Void p) {
        //JmlMethodClauseExpr copy = (JmlMethodClauseExpr)super.visitJmlMethodClauseExpr(that, p);
        JmlExpressionVisitor expressionVisitor = new JmlExpressionVisitor(context, M, baseVisitor, translationMode, oldVars, returnVar, currentMethod);

        if(that.clauseKind.name().equals("ensures")) {
            expressionVisitor.setTranslationMode(TranslationMode.ASSERT);
            translationMode = TranslationMode.ASSERT;
        } else if(that.clauseKind.name().equals("requires")) {
            expressionVisitor.setTranslationMode(TranslationMode.ASSUME);
            translationMode = TranslationMode.ASSUME;
        }
        JCExpression normalized = NormalizeVisitor.normalize(that.expression, context, M);
        JCExpression copy = expressionVisitor.copy(normalized);
        newStatements = expressionVisitor.getNewStatements();
        oldVars = expressionVisitor.getOldVars();
        newStatements = newStatements.prependList(expressionVisitor.getNeededVariableDefs());
        newStatements = newStatements.append(transUtils.makeAssumeOrAssertStatement(copy, translationMode));
        if(translationMode == TranslationMode.ASSERT) {
            combinedNewEnsStatements = combinedNewEnsStatements.append(M.Block(0L, newStatements));
        } else if(translationMode == TranslationMode.ASSUME) {
            combinedNewReqStatements = combinedNewReqStatements.append(M.Block(0L, newStatements));
        }
        newStatements = List.nil();
        translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        return M.JmlMethodClauseExpr(that.clauseKind.name(), that.clauseKind, copy);
    }

    @Override
    public JCTree visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that, Void p) {
        if(currentAssignable == null) {
            currentAssignable = List.nil();
        }
        if(that.list != null) {
            if(that.list.stream().anyMatch(loc -> loc instanceof JmlStoreRefKeyword
            && ((JmlStoreRefKeyword) loc).token.equals(JmlTokenKind.BSNOTHING))) {
                if(that.list.size() + currentAssignable.size() > 1) {
                    throw new RuntimeException("Assignable containing \\nothing and something else is not valid.");
                }
            } else {
                currentAssignable = currentAssignable.appendList(that.list);
            }
        }
        return super.visitJmlMethodClauseStoreRef(that, p);
    }

    @Override
    public JCTree visitJmlStatementSpec(JmlStatementSpec that, Void p) {
        return that;
    }

    @Override
    public JCTree visitJmlMethodDecl(JmlMethodDecl that, Void p) {
        requiresList.clear();
        ensuresList.clear();
        currentAssignable = null;
        currentMethod = (JmlMethodDecl)that.clone();
        if(currentMethod.mods.getFlags().contains(Modifier.ABSTRACT)) {
            return currentMethod;
        }
        hasReturn = false;
        JCVariableDecl returnVar = null;
        Type t = that.sym.getReturnType();
        if(!(t instanceof Type.JCVoidType)) {
            returnVar = treeutils.makeVarDef(t, M.Name("returnVar"), currentMethod.sym, getLiteralForType(t));
            hasReturn = true;
            this.returnVar = returnVar.sym;
        } else {
            this.returnVar = null;
        }
        JmlMethodDecl copy = (JmlMethodDecl)visitJmlMethodDeclBugfix(that, p);
        JCVariableDecl catchVar = treeutils.makeVarDef(syms.exceptionType, M.Name("e"), currentMethod.sym, Position.NOPOS);
        JCExpression ty = M.at(that).Type(syms.runtimeExceptionType);
        JCExpression msg = treeutils.makeStringLiteral(that.pos, "Specification is not well defined for method " + that.getName());
        JCThrow throwStmt = M.Throw(M.NewClass(null, null, ty, List.of(msg), null));
//        JCTry reqTry = M.Try(M.Block(0L, List.from(combinedNewReqStatements)),
//                List.of(M.Catch(catchVar, M.Block(0L, List.of(throwStmt)))), null);
//        JCTry ensTry = M.Try(M.Block(0L, List.from(combinedNewEnsStatements)),
//                List.of(M.Catch(catchVar, M.Block(0L, List.of(throwStmt)))), null);

        JCVariableDecl catchVarb = treeutils.makeVarDef(baseVisitor.getExceptionClass().type, M.Name("ex"), currentMethod.sym, Position.NOPOS);

        List< JCStatement> l = List.nil();

        JCReturn returnStmt = null;
        if(returnVar != null) {
            returnStmt = M.Return(M.Ident(returnVar));
        }

        List<JCStatement> body = List.nil();
        if(that.body != null) {
            body = transformBody(that.body.getStatements());
        }
        JCTry bodyTry = M.Try(M.Block(0L, body),
                List.of(
                        M.Catch(catchVarb, M.Block(0L, List.nil()))
                ),
                null);
        if(combinedNewReqStatements.size() > 0) {
            l = l.appendList(combinedNewReqStatements);
        }

        //adding the variable for old clauses
        for(JCVariableDecl variableDecl : oldVars.values()) {
            l = l.append(variableDecl);
        }

        if(returnVar != null) {
            l = l.append(returnVar);
        }
        l = l.append(bodyTry);
        l = l.appendList(combinedNewEnsStatements);
        if(returnStmt != null) {
            l = l.append(returnStmt);
        }


        currentMethod.body = M.Block(0L, l);

        currentMethod.methodSpecsCombined = null;
        currentMethod.cases = null;
        combinedNewReqStatements = List.nil();
        combinedNewEnsStatements = List.nil();

        return currentMethod;
    }

    private List<JCStatement> transformBody(List<JCStatement> oBody) {
        List<JCStatement> body = List.nil();
        for(JCStatement st : oBody) {
            if(!st.toString().equals("super();")) {
                JmlExpressionVisitor ev = new JmlExpressionVisitor(context, M, baseVisitor, translationMode, oldVars, this.returnVar, currentMethod);
                if (currentAssignable == null) {
                    currentAssignable = List.of(M.JmlStoreRefKeyword(JmlTokenKind.BSEVERYTHING));
                }
                ev.setCurrentAssignable(currentAssignable);
                JCStatement copy = ev.copy(st);
                if (ev.getNewStatements().size() == 0) {
                    body = body.append(copy);
                } else {
                    body = body.appendList(ev.getNewStatements());
                }
            }
        }
        return body;
    }

    public JCTree visitJmlMethodDeclBugfix(JmlMethodDecl that, Void p) {
        JmlMethodDecl copy = (JmlMethodDecl)visitMethodWithoutBody(that, p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl;
        //copy.cases = (JmlMethodSpecs)this.copy((JCTree)that.cases, (Object)p);
        copy.methodSpecsCombined = JmlSpecs.copy(that.methodSpecsCombined, p, this);
        copy.cases = (JmlMethodSpecs)copy.methodSpecsCombined.cases.clone();
        copy.type = that.type;
        return copy;
    }

    public JCTree visitMethodWithoutBody(MethodTree node, Void p) {
        JCMethodDecl t = (JCMethodDecl)node;
        JCModifiers mods = (JCModifiers)this.copy((JCTree)t.mods, p);
        JCExpression restype = (JCExpression)this.copy((JCTree)t.restype, p);
        List<JCTypeParameter> typarams = this.copy(t.typarams, p);
        List<JCVariableDecl> params = this.copy(t.params, p);
        JCVariableDecl recvparam = (JCVariableDecl)this.copy((JCTree)t.recvparam, p);
        List<JCExpression> thrown = this.copy(t.thrown, p);
        JCBlock body = M.Block(0L, List.nil());
        JCExpression defaultValue = (JCExpression)this.copy((JCTree)t.defaultValue, p);
        return this.M.at(t.pos).MethodDef(mods, t.name, restype, typarams, recvparam, params, thrown, body, defaultValue);
    }

    private JCLiteral getLiteralForType(Type t) {
        if(t.getTag().equals(TypeTag.INT)) {
            return M.Literal(0);
        }
        if(t.getTag().equals(TypeTag.LONG)) {
            return M.Literal(0);
        }
        if(t.getTag().equals(TypeTag.DOUBLE)) {
            return M.Literal(0.0);
        }
        if(t.getTag().equals(TypeTag.FLOAT)) {
            return M.Literal(0.0f);
        }
        if(t.getTag().equals(TypeTag.SHORT)) {
            return M.Literal(0);
        }
        if(t.getTag().equals(TypeTag.BOOLEAN)) {
            return M.Literal(true);
        }
        if(t.getTag().equals(TypeTag.CHAR)) {
            return M.Literal(0);
        }
        return treeutils.nullLit;
    }
}
