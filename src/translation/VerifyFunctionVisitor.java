package translation;

import static com.sun.tools.javac.tree.JCTree.JCAnnotation;
import static com.sun.tools.javac.tree.JCTree.JCBlock;
import static com.sun.tools.javac.tree.JCTree.JCExpression;
import static com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import static com.sun.tools.javac.tree.JCTree.JCIdent;
import static com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import static com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import static com.sun.tools.javac.tree.JCTree.JCModifiers;
import static com.sun.tools.javac.tree.JCTree.JCReturn;
import static com.sun.tools.javac.tree.JCTree.JCStatement;
import static com.sun.tools.javac.tree.JCTree.JCTry;
import static com.sun.tools.javac.tree.JCTree.JCTypeParameter;
import static com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import static org.jmlspecs.openjml.JmlTree.JmlAnnotation;
import static org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import static org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import static org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import static org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import static org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import static org.jmlspecs.openjml.JmlTree.JmlStatementSpec;
import static org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword;
import static org.jmlspecs.openjml.JmlTree.Maker;

import cli.CLI;
import cli.ErrorLogger;
import com.sun.source.tree.MethodTree;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import exceptions.TranslationException;
import exceptions.UnsupportedException;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import javax.lang.model.element.Modifier;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.ext.AssignableClauseExtension;
import utils.NormalizeVisitor;
import utils.TranslationUtils;

/**
 * Created by jklamroth on 11/13/18.
 *
 * <p> This Visitor translates methods and their translation into Java!? </p>
 */
public class VerifyFunctionVisitor extends FilterVisitor {
    private final Maker maker;
    private final Context context;
    private final Symtab syms;
    private final JmlTreeUtils treeutils;
    private final ClassReader reader;
    private final BaseVisitor baseVisitor;
    protected JmlMethodDecl currentMethod;
    private List<JCStatement> newStatements = List.nil();
    private List<JCStatement> combinedNewReqStatements = List.nil();
    private List<JCStatement> combinedNewEnsStatements = List.nil();
    private List<List<JCStatement>> reqCases = List.nil();
    private List<List<JCStatement>> ensCases = List.nil();
    private List<List<JCExpression>> assCases = List.nil();
    private List<JCExpression> signaledExceptions = List.nil();
    private Symbol returnVarSym = null;
    private boolean hasReturn = false;
    private VerifyFunctionVisitor.TranslationMode translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
    //Has to perserve order (e.g. LinkedHashMap)
    private LinkedHashMap<JCExpression, JCVariableDecl> oldVars = new LinkedHashMap<>();
    private List<JCStatement> oldInits = List.nil();
    private List<JCExpression> currentAssignable = null;


    public VerifyFunctionVisitor(Context context, Maker maker, BaseVisitor base) {
        super(context, maker);
        baseVisitor = base;
        this.context = context;
        this.maker = Maker.instance(context);
        this.syms = Symtab.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
    }

    @Override
    public JCTree visitJmlMethodClauseExpr(JmlMethodClauseExpr that, Void p) {
        TranslationUtils.setCurrentASTNode(that);
        //JmlMethodClauseExpr copy = (JmlMethodClauseExpr)super.visitJmlMethodClauseExpr(that, p);
        JmlExpressionVisitor expressionVisitor =
            new JmlExpressionVisitor(context, maker, baseVisitor, translationMode, oldVars, returnVarSym, currentMethod);

        if (that.clauseKind.name().equals("ensures")) {
            expressionVisitor.setTranslationMode(TranslationMode.ASSERT);
            TranslationUtils.setCurrentEnsures(that);
            translationMode = TranslationMode.ASSERT;
        } else if (that.clauseKind.name().equals("requires")) {
            expressionVisitor.setTranslationMode(TranslationMode.ASSUME);
            translationMode = TranslationMode.ASSUME;
        } else if (that.clauseKind.name().equals("assignable")) {
            //Nothing to do here
            ;
        } else {
            throw new UnsupportedException("Unsupported clause type: " + that.clauseKind + " (" + that + ")");
        }
        JCExpression normalized = NormalizeVisitor.normalize(that.expression, context, maker);
        JCExpression copy = expressionVisitor.copy(normalized);
        newStatements = expressionVisitor.getNewStatements();
        oldVars.putAll(expressionVisitor.getOldVars());
        oldInits = oldInits.appendList(expressionVisitor.getOldInits());
        newStatements = newStatements.prependList(expressionVisitor.getNeededVariableDefs());
        newStatements = newStatements.append(TranslationUtils.makeAssumeOrAssertStatement(copy, translationMode));
        if (translationMode == TranslationMode.ASSERT) {
            JCBlock b = maker.Block(0L, newStatements);
            combinedNewEnsStatements = combinedNewEnsStatements.append(b);
        } else if (translationMode == TranslationMode.ASSUME) {
            combinedNewReqStatements = combinedNewReqStatements.append(maker.Block(0L, newStatements));
        }
        newStatements = List.nil();
        translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        return maker.JmlMethodClauseExpr(that.clauseKind.name(), that.clauseKind, copy);
    }

    @Override
    public JCTree visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that, Void p) {
        TranslationUtils.setCurrentASTNode(that);
        if (currentAssignable == null) {
            currentAssignable = List.nil();
        }
        if (that.list != null) {
            currentAssignable = currentAssignable.appendList(that.list);
            TranslationUtils.setCurrentAssignable(M.JmlMethodClauseStoreRef(that.keyword, that.clauseKind, currentAssignable));
        }

        return M.JmlMethodClauseStoreRef("assignable",
                AssignableClauseExtension.assignableClauseKind,
                List.of(M.JmlStoreRefKeyword(JmlTokenKind.BSNOTHING)));
    }

    @Override
    public JCTree visitJmlStatementSpec(JmlStatementSpec that, Void p) {
        return that;
    }

    @Override
    public JCTree visitJmlSpecificationCase(JmlSpecificationCase that, Void p) {
        combinedNewEnsStatements = List.nil();
        combinedNewReqStatements = List.nil();
        currentAssignable = List.nil();
        JCTree copy = super.visitJmlSpecificationCase(that, p);

        if (TranslationUtils.isPure(currentMethod)) {
            currentAssignable = currentAssignable.append(maker.JmlStoreRefKeyword(JmlTokenKind.BSNOTHING));
        }

        ensCases = ensCases.append(combinedNewEnsStatements);
        reqCases = reqCases.append(combinedNewReqStatements);
        assCases = assCases.append(currentAssignable);
        combinedNewEnsStatements = List.nil();
        combinedNewReqStatements = List.nil();
        currentAssignable = List.nil();
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseSigOnly(JmlTree.JmlMethodClauseSignalsOnly that, Void p) {
        signaledExceptions = signaledExceptions.appendList(that.list);
        return super.visitJmlMethodClauseSigOnly(that, p);
    }

    @Override
    public JCTree visitJmlMethodDecl(JmlMethodDecl that, Void p) {
        currentMethod = (JmlMethodDecl) that.clone();
        if (currentMethod.mods.getFlags().contains(Modifier.ABSTRACT)) {
            return currentMethod;
        }
        hasReturn = false;
        JCVariableDecl returnVar = null;
        Type t = that.sym.getReturnType();
        if (!(t instanceof Type.JCVoidType)) {
            returnVar = treeutils.makeVarDef(t, maker.Name("returnVar"), currentMethod.sym, TranslationUtils.getLiteralForType(t));
            hasReturn = true;
            this.returnVarSym = returnVar.sym;
        } else {
            this.returnVarSym = null;
        }

        if (that.mods.annotations != null) {
            for (JCAnnotation a : that.mods.annotations) {
                if (a instanceof JmlAnnotation) {
                    if (a.annotationType.toString().endsWith(".Pure")) {
                        ErrorLogger.warn("\"pure\" annotations a currently only translated as assignable \\nothing.");
                    }
                }
            }
        }

        oldVars = new LinkedHashMap<>();
        oldInits = List.nil();
        currentMethod = (JmlMethodDecl) visitJmlMethodDeclBugfix(that, p);
        currentMethod.sym = that.sym;
        List<JCStatement> invariantAssert = List.nil();
        List<JCStatement> oldInitsInv = List.nil();
        LinkedHashMap<JCExpression, JCVariableDecl> oldVarsInv = new LinkedHashMap<>();
        for (JCExpression expression : baseVisitor.getInvariants()) {
            expression = NormalizeVisitor.normalize(expression, context, maker);
            JmlExpressionVisitor ev =
                new JmlExpressionVisitor(context, maker, baseVisitor, TranslationMode.ASSERT, oldVars, this.returnVarSym, currentMethod);
            JCExpression invCopy = ev.copy(expression);
            oldVars.putAll(ev.getOldVars());
            oldInits = oldInits.appendList(ev.getOldInits());
            oldInitsInv = oldInitsInv.appendList(ev.getOldInits());
            invariantAssert = invariantAssert.prependList(ev.getNeededVariableDefs());
            invariantAssert = invariantAssert.appendList(ev.getNewStatements());
            invariantAssert = invariantAssert.append(TranslationUtils.makeAssumeOrAssertStatement(invCopy, TranslationMode.ASSERT));
        }
        List<JCStatement> invariantAssume = List.nil();
        for (JCExpression expression : baseVisitor.getInvariants()) {
            expression = NormalizeVisitor.normalize(expression, context, maker);
            JmlExpressionVisitor ev =
                new JmlExpressionVisitor(context, maker, baseVisitor, TranslationMode.ASSUME, oldVars, this.returnVarSym, currentMethod);
            JCExpression invCopy = ev.copy(expression);
            oldVarsInv.putAll(ev.getOldVars());
            oldInitsInv = oldInitsInv.appendList(ev.getOldInits());
            invariantAssume = invariantAssume.prependList(ev.getNeededVariableDefs());
            invariantAssume = invariantAssume.appendList(ev.getNewStatements());
            invariantAssume = invariantAssume.append(TranslationUtils.makeAssumeOrAssertStatement(invCopy, TranslationMode.ASSUME));
        }

        if (ensCases.size() != reqCases.size() || ensCases.size() != assCases.size()) {
            throw new TranslationException("Different number of cases for method: " + currentMethod.name.toString());
        }
        int caseIdx = Math.min(CLI.caseIdx, ensCases.size() - 1);
        if (caseIdx < 0) {
            return null;
        }
        oldVars.putAll(oldVarsInv);
        oldInits = oldInits.appendList(oldInitsInv);

        JCVariableDecl catchVarb =
            treeutils.makeVarDef(baseVisitor.getExceptionClass().type, maker.Name("ex"), currentMethod.sym, TranslationUtils.getCurrentPosition());

        List<JCStatement> l = List.nil();

        JCReturn returnStmt = null;
        if (returnVar != null) {
            returnStmt = maker.Return(maker.Ident(returnVar));
        }

        List<JCStatement> body = List.nil();

        if (that.body != null) {
            body = transformBody(that.body.getStatements(), caseIdx, currentMethod);
        }

        //If this is a constructor and this() or super() is called they have to be the first statement
        if (body.size() > 0) {
            if (body.get(0) instanceof JCExpressionStatement) {
                JCExpressionStatement stmt = (JCExpressionStatement) body.get(0);
                if (stmt.expr instanceof JCMethodInvocation) {
                    JCMethodInvocation thisCall = (JCMethodInvocation) stmt.expr;
                    if (thisCall.meth instanceof JCIdent) {
                        Name name = ((JCIdent) thisCall.meth).getName();
                        if (name.toString().equals("this") || name.toString().equals("super")) {
                            l = l.append(body.head);
                            body = body.tail;
                        }
                    }
                }
            }
        }

        List<JCTree.JCCatch> catches = List.of(maker.Catch(catchVarb, maker.Block(0L, List.nil())));
        for (JCExpression exceptionType : signaledExceptions) {
            JCVariableDecl catchVar =
                    treeutils.makeVarDef(exceptionType.type, maker.Name("e"), currentMethod.sym, TranslationUtils.getCurrentPosition());
            JCStatement assumeFalse = TranslationUtils.makeAssumeStatement(M.Literal(false));
            catches = catches.append(maker.Catch(catchVar, maker.Block(0L, List.of(assumeFalse))));
        }

        JCTry bodyTry = maker.Try(maker.Block(0L, body),
            catches,
            null);

        //assume invariants if its not a constructor
        long check = that.getModifiers().flags & 8L;
        if (check == 0 && !that.getName().toString().contains("<init>")) {
            l = l.append(maker.Block(0L, invariantAssume));
        }

        l = l.appendList(reqCases.get(caseIdx));

        //adding the variable for old clauses
        for (JCVariableDecl variableDecl : oldVars.values()) {
            l = l.append(variableDecl);
        }

        for (JCStatement oldInit : oldInits) {
            l = l.append(oldInit);
        }

        if (returnVar != null) {
            l = l.append(returnVar);
        }

        //if its a constructor the body may not be wrapped in a try because of the initialization of final fields
        if (!that.getName().toString().contains("<init>")) {
            l = l.append(bodyTry);
        } else {
            l = l.appendList(body);
        }


        l = l.appendList(ensCases.get(caseIdx));

        //assert invariants
        if (check == 0 && !TranslationUtils.isPure(currentMethod)) {
            l = l.append(maker.Block(0L, invariantAssert));
        }

        if (CLI.doSanityCheck) {
            l = l.append(TranslationUtils.makeAssertStatement(maker.Literal(false)));
        }
        if (returnStmt != null) {
            l = l.append(returnStmt);
        }

        currentMethod.body = maker.Block(0L, l);

        currentMethod.methodSpecsCombined = null;
        currentMethod.cases = null;
        ensCases = List.nil();
        reqCases = List.nil();
        combinedNewEnsStatements = List.nil();
        combinedNewReqStatements = List.nil();
        signaledExceptions = List.nil();
        JmlExpressionVisitor.currentFreshLocations = new ArrayList<>();
        if (!currentMethod.name.toString().equals("<init>")) {
            currentMethod.name = maker.Name(currentMethod.name.toString() + "Verf");
        }
        return currentMethod;
    }

    private List<JCStatement> transformBody(List<JCStatement> bodyList, int caseIdx, JmlMethodDecl currentMethod) {
        List<JCExpression> currentAssignable = assCases.get(caseIdx);
        if (currentAssignable == null || currentAssignable.size() == 0) {
            currentAssignable = List.of(maker.JmlStoreRefKeyword(JmlTokenKind.BSEVERYTHING));
        }
        if (currentAssignable.size() == 1 && currentAssignable.get(0) instanceof JmlStoreRefKeyword &&
            ((JmlStoreRefKeyword) currentAssignable.get(0)).token.equals(JmlTokenKind.BSNOTHING)) {
            currentAssignable = List.nil();
        }
        List<JCStatement> body = List.nil();
        List<JCStatement> variableDefs = List.nil();
        for (JCStatement st : bodyList) {
            if (!st.toString().equals("super();")) {
                JmlExpressionVisitor ev =
                    new JmlExpressionVisitor(context, maker, baseVisitor, translationMode, oldVars, this.returnVarSym, currentMethod);
                ev.setCurrentAssignable(currentAssignable);
                TranslationUtils.setCurrentASTNode(st);
                JCStatement copy = ev.copy(st);
                if (ev.getNewStatements().size() == 0) {
                    body = body.append(copy);
                } else {
                    variableDefs = variableDefs.appendList(ev.getNeededVariableDefs());
                    body = body.appendList(ev.getNewStatements());
                }
            }
        }
        body = body.prependList(variableDefs);
        return body;
    }

    public JCTree visitJmlMethodDeclBugfix(JmlMethodDecl that, Void p) {
        JmlMethodDecl copy = (JmlMethodDecl) visitMethodWithoutBody(that, p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl;
        //copy.cases = (JmlMethodSpecs)this.copy((JCTree)that.cases, (Object)p);
        copy.methodSpecsCombined = JmlSpecs.copy(that.methodSpecsCombined, p, this);
        copy.cases = (JmlMethodSpecs) copy.methodSpecsCombined.cases.clone();
        copy.type = that.type;
        return copy;
    }

    public JCTree visitMethodWithoutBody(MethodTree node, Void p) {
        JCMethodDecl t = (JCMethodDecl) node;
        JCModifiers mods = (JCModifiers) this.copy((JCTree) t.mods, p);
        JCExpression restype = (JCExpression) this.copy((JCTree) t.restype, p);
        List<JCTypeParameter> typarams = this.copy(t.typarams, p);
        List<JCVariableDecl> params = this.copy(t.params, p);
        JCVariableDecl recvparam = (JCVariableDecl) this.copy((JCTree) t.recvparam, p);
        List<JCExpression> thrown = this.copy(t.thrown, p);
        JCBlock body = maker.Block(0L, List.nil());
        JCExpression defaultValue = (JCExpression) this.copy((JCTree) t.defaultValue, p);
        return this.maker.at(t.pos).MethodDef(mods, t.name, restype, typarams, recvparam, params, thrown, body, defaultValue);
    }

    public enum TranslationMode {
        ASSUME,
        ASSERT,
        JAVA,
        DEMONIC
    }
}
