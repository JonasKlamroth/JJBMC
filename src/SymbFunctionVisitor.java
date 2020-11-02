import com.sun.source.tree.MethodInvocationTree;
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
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;

import javax.lang.model.element.Modifier;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static com.sun.tools.javac.tree.JCTree.*;
import static org.jmlspecs.openjml.JmlTree.*;

/**
 * Created by jklamroth on 12/10/18.
 *
 * This visitor is used to create the second form of a specified method which is used
 * if this method is invoked. It mainly asserts the precondition and assumes the postcondition.
 */
public class SymbFunctionVisitor extends JmlTreeCopier {
    private final Maker M;
    private final Context context;
    private final Symtab syms;
    private final JmlTreeUtils treeutils;
    private final ClassReader reader;
    private Set<JCExpression> ensuresList = new HashSet<>();
    private Set<JCExpression> requiresList = new HashSet<>();
    private JmlMethodDecl currentMethod;
    private List<JCStatement> newStatements = List.nil();
    private List<JCStatement> combinedNewReqStatements = List.nil();
    private List<JCStatement> combinedNewEnsStatements = List.nil();
    private Symbol returnVar = null;
    private boolean hasReturn = false;
    private VerifyFunctionVisitor.TranslationMode translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
    private LinkedHashMap<JCExpression, JCVariableDecl> oldVars = new LinkedHashMap<>();
    private List<JCStatement> oldInits = List.nil();
    private  final BaseVisitor baseVisitor;
    private List<JCExpression> currentAssignable = List.nil();
    private Symbol currentSymbol = null;
    private boolean inConstructor = false;

    public SymbFunctionVisitor(Context context, Maker maker, BaseVisitor base) {
        super(context, maker);
        baseVisitor = base;
        this.context = context;
        this.M = Maker.instance(context);
        this.syms = Symtab.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
    }

    @Override
    public JCTree visitJmlMethodClauseExpr(JmlMethodClauseExpr that, Void p) {
        //JmlMethodClauseExpr copy = (JmlMethodClauseExpr)super.visitJmlMethodClauseExpr(that, p);
        JmlExpressionVisitor expressionVisitor = new JmlExpressionVisitor(context, M, baseVisitor, translationMode, oldVars, returnVar, currentMethod);
        if(that.clauseKind.name().equals("ensures")) {
            expressionVisitor.setTranslationMode(VerifyFunctionVisitor.TranslationMode.ASSUME);
            translationMode = VerifyFunctionVisitor.TranslationMode.ASSUME;
        } else if(that.clauseKind.name().equals("requires")) {
            expressionVisitor.setTranslationMode(VerifyFunctionVisitor.TranslationMode.ASSERT);
            translationMode = VerifyFunctionVisitor.TranslationMode.ASSERT;
        }
        expressionVisitor.inConstructor = this.inConstructor;
        JCExpression normalized = NormalizeVisitor.normalize(that.expression, context, M);
        JCExpression copy = expressionVisitor.copy(normalized);
        newStatements = expressionVisitor.getNewStatements();
        newStatements = newStatements.prependList(expressionVisitor.getNeededVariableDefs());
        oldVars = expressionVisitor.getOldVars();
        oldInits = expressionVisitor.getOldInits();
        if(translationMode == VerifyFunctionVisitor.TranslationMode.ASSUME) {
            newStatements = List.of(M.Block(0L, newStatements.append(TranslationUtils.makeAssumeStatement(copy))));
            combinedNewEnsStatements = combinedNewEnsStatements.appendList(newStatements);
        } else if(translationMode == VerifyFunctionVisitor.TranslationMode.ASSERT){
            newStatements = List.of(M.Block(0L, newStatements.append(TranslationUtils.makeAssertStatement(copy))));
            combinedNewReqStatements = combinedNewReqStatements.appendList(newStatements);
        }
        newStatements = List.nil();
        translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        return M.JmlMethodClauseExpr(that.clauseKind.name(), that.clauseKind, copy);
    }

    @Override
    public JCTree visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that, Void p) {
        currentAssignable = currentAssignable.appendList(that.list);
        return super.visitJmlMethodClauseStoreRef(that, p);
    }

    @Override
    public JCTree visitJmlStatementSpec(JmlStatementSpec that, Void p) {
        return that;
    }

    @Override
    public JCTree visitJmlMethodDecl(JmlMethodDecl that, Void p) {
        currentSymbol = that.sym;
        requiresList.clear();
        ensuresList.clear();
        currentAssignable = List.nil();
        currentMethod = (JmlMethodDecl)that.clone();
        hasReturn = false;

        if(that.cases == null) {
            JmlMethodDecl copy = (JmlMethodDecl)visitJmlMethodDeclBugfix(that, p);
            copy.name = M.Name(copy.name.toString() + "Symb");
            copy.mods.annotations = List.nil();
            if(copy.mods.getFlags().contains(Modifier.ABSTRACT)) {
                copy.mods.flags &= 1024;
            }
            if(that.getName().toString().equals("<init>")) {
                List<JCExpression> l = List.nil();
                for(JCVariableDecl vd : currentMethod.params) {
                    l = l.append(M.Ident(vd));
                }
                JCReturn ret = M.Return(M.NewClass(null, null, M.at(Position.NOPOS).Type(currentSymbol.owner.type), l, null));
                copy.body = M.Block(0L, List.of(ret));
                copy.restype = M.Ident(copy.sym.owner.name);
                copy.name = M.Name(copy.sym.owner.name + "Symb");
                //Make it static
                copy.mods.flags |= 8L;
                //Make it public
                copy.mods.flags |= 1L;
                //Make it not private and not protected
                copy.mods.flags &= (~2L);
                copy.mods.flags &= (~4L);
            }
            return copy;
        }
        currentSymbol = that.sym;
        requiresList.clear();
        ensuresList.clear();
        currentAssignable = List.nil();
        currentMethod = (JmlMethodDecl)that.clone();
        hasReturn = false;

        JCVariableDecl returnVar = null;
        Type t = that.sym.getReturnType();

        if(!(t instanceof Type.JCVoidType)) {
            returnVar = treeutils.makeVarDef(t, M.Name("returnVar"), currentMethod.sym, TranslationUtils.getNondetFunctionForType(t, currentMethod.sym));
            hasReturn = true;
            this.returnVar = returnVar.sym;
        } else if(that.name.toString().equals("<init>")) {
            this.inConstructor = true;
            List<JCExpression> l = List.nil();
            for(JCVariableDecl vd : currentMethod.params) {
                l = l.append(M.Ident(vd));
            }
            JCNewClass initVal = M.NewClass(null, null, M.at(Position.NOPOS).Type(currentSymbol.owner.type), l, null);
            returnVar = treeutils.makeVarDef(currentMethod.sym.owner.type, M.Name("returnVar"), currentMethod.sym, initVal);
            hasReturn = true;
            this.returnVar = returnVar.sym;
        } else {
            this.returnVar = null;
        }

        if(that.name.toString().equals("<init>")) {
            inConstructor = true;
        }
        JmlMethodDecl copy = (JmlMethodDecl)visitJmlMethodDeclBugfix(that, p);
        if(copy.name.toString().equals("<init>")) {
            copy.mods.flags &= 8L;
            copy.restype = M.Ident(copy.sym.owner.name);
            inConstructor = false;
        }
        JCVariableDecl catchVar = treeutils.makeVarDef(syms.exceptionType, M.Name("e"), currentMethod.sym, Position.NOPOS);
        JCExpression ty = M.at(that).Type(syms.runtimeExceptionType);
        JCExpression msg = treeutils.makeStringLiteral(that.pos, "Specification is not well defined for method " + that.getName());
        JCThrow throwStmt = M.Throw(M.NewClass(null, null, ty, List.of(msg), null));
        List<JCExpression> assignables = baseVisitor.getAssignablesForName(that.getName().toString());
        List<JCStatement> assignableConditions = List.nil();
        JCTry reqTry = M.Try(M.Block(0L, List.from(combinedNewReqStatements)),
                List.of(M.Catch(catchVar, M.Block(0L, List.of(throwStmt)))), null);
        JCTry ensTry = M.Try(M.Block(0L, List.from(combinedNewEnsStatements)),
                List.of(M.Catch(catchVar, M.Block(0L, List.of(throwStmt)))), null);

        List< JCStatement> l = List.nil();
        List<JCStatement> bodyStats = List.nil();
        for(JCVariableDecl variableDecl : oldVars.values()) {
            bodyStats = bodyStats.append(variableDecl);
        }

        for(JCStatement oldInit : oldInits) {
            bodyStats = bodyStats.append(oldInit);
        }

        bodyStats = bodyStats.appendList(TranslationUtils.havoc(currentAssignable, copy.sym, this));

        if(hasReturn) {
            if(returnVar != null) {
                List< JCStatement> l1 = List.nil();
                JCReturn returnStmt = M.Return(M.Ident(returnVar));
                if(combinedNewEnsStatements.size() > 0) {
                    l1 = l1.append(ensTry);
                }
                l1 = l1.append(returnStmt);
                if(combinedNewReqStatements.size() > 0) {
                    l = l.append(reqTry);
                }

                l = l.append(returnVar);
                if(copy.name.toString().equals("<init>")) {
                    l = l.append(TranslationUtils.makeAssumeOrAssertStatement(treeutils.makeNeqObject(Position.NOPOS, M.Ident(returnVar), treeutils.makeNullLiteral(Position.NOPOS)), VerifyFunctionVisitor.TranslationMode.ASSUME));
                }
                l = l.appendList(bodyStats).appendList(l1);
            } else {
                if(combinedNewEnsStatements.size() > 0) {
                    l = l.append(reqTry).append(ensTry);
                } else {
                    l = bodyStats;
                    l = l.prepend(reqTry);
                }
            }
        } else {
            //l = copy.body.getStatements();
            l = bodyStats;
            if(combinedNewEnsStatements.size() > 0) {
                l = l.append(ensTry);
            }
            if(combinedNewReqStatements.size() > 0) {
                l = l.prepend(reqTry);
            }
        }
        copy.body = M.Block(0L, l);

        copy.methodSpecsCombined = null;
        copy.cases = null;
        if(copy.name.toString().equals("<init>")) {
            copy.name = M.Name(copy.sym.owner.name + "Symb");
            //Make it static
            copy.mods.flags |= 8L;
            //Make it public
            copy.mods.flags |= 1L;
            //Make it not private and not protected
            copy.mods.flags &= (~2L);
            copy.mods.flags &= (~4L);
        } else {
            copy.name = M.Name(currentMethod.name.toString() + "Symb");
        }
        copy.mods.annotations = List.nil();
        combinedNewReqStatements = List.nil();
        combinedNewEnsStatements = List.nil();
        if(copy.mods.getFlags().contains(Modifier.ABSTRACT)) {
            copy.mods.flags ^= 1024;
        }
        inConstructor = false;
        return copy;
    }

    public JCTree visitJmlMethodDeclBugfix(JmlMethodDecl that, Void p) {
        JmlMethodDecl copy = (JmlMethodDecl)super.visitMethod(that, p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl;
        //copy.cases = (JmlMethodSpecs)this.copy((JCTree)that.cases, (Object)p);
        copy.methodSpecsCombined = JmlSpecs.copy(that.methodSpecsCombined, p, this);
        copy.cases = (JmlMethodSpecs)copy.methodSpecsCombined.cases.clone();
        copy.type = that.type;
        return copy;
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
        return treeutils.nullLit;
    }

    public JCExpression editAssignable(JCExpression e) {
        return editAssignable(e, false);
    }

    public JCExpression editAssignable(JCExpression e, boolean ignoreLocals) {
        if(e instanceof JCIdent) {
            if(!ignoreLocals && ((JCIdent) e).sym.owner.equals(currentSymbol)) {
                return M.Literal(false);
            }
            return editAssignable((JCIdent)e);
        } else if(e instanceof JmlStoreRefArrayRange) {
            return editAssignable((JmlStoreRefArrayRange) e);
        } else if(e instanceof JCArrayAccess) {
            JCExpression expr =  ((JCArrayAccess) e).indexed;
            if(expr instanceof JCIdent) {
                if(((JCIdent) expr).sym.owner.equals(currentSymbol)) {
                    return M.Literal(false);
                }
            } else if(expr instanceof JCFieldAccess) {
                if(((JCFieldAccess) expr).sym.owner.equals(currentSymbol)) {
                    return M.Literal(false);
                }
            } else {
                throw new RuntimeException("Unexpected type.");
            }
            return editAssignable((JCArrayAccess) e);
        } else if(e instanceof JCFieldAccess) {
            /*if(((JCFieldAccess) e).sym.owner.equals(currentSymbol) && !params.contains(((JCFieldAccess) e).sym)) {
                return M.Literal(false);
            }*/
            return editAssignable((JCFieldAccess) e);
        } else if(e instanceof JmlStoreRefKeyword) {
            JmlStoreRefKeyword k = (JmlStoreRefKeyword)e;
            if(k.token == JmlTokenKind.BSNOTHING) {
                return M.Literal(false);
            } else if(k.token == JmlTokenKind.BSEVERYTHING) {
                return M.Literal(currentAssignable.stream().noneMatch(loc -> loc instanceof JmlStoreRefKeyword));
            } else {
                throw new RuntimeException("Cannot handle assignment to " + e.toString());
            }
        } else {
            throw new RuntimeException("Could not handle assignment to " + e.toString());
        }
    }

    public JCExpression editAssignable(JCIdent e) {
        if(e.type.isPrimitive()) {
            if(currentAssignable.stream().filter(as -> as instanceof JCIdent)
                    .noneMatch(as -> ((JCIdent)as).sym.equals(e.sym))) {
                return M.Literal(true);
            }
            return M.Literal(false);
        } else {
            if(currentAssignable.stream().anyMatch(
                    fa -> fa instanceof JCFieldAccess &&
                            ((JCFieldAccess) fa).name == null &&
                            ((JCFieldAccess) fa).selected.toString().equals("this"))) {
                return M.Literal(false);
            }
            List<JCIdent> pot = List.from(currentAssignable.stream().filter(as -> as instanceof JCIdent)
                    .map(as -> (JCIdent)as)
                    .filter(as -> !as.type.isPrimitive())
                    .filter(as -> isSuperType(as.type , e.type) || isSuperType(e.type , as.type))
                    .collect(Collectors.toList()));
            if(pot.size() == 0) {
                return M.Literal(true);
            }
            JCExpression expr = treeutils.makeNeqObject(Position.NOPOS, pot.get(0), e);
            if(!pot.get(0).sym.owner.equals(currentSymbol) && !pot.get(0).toString().startsWith("this.")) {
                expr = treeutils.makeNeqObject(Position.NOPOS, M.Ident("this." + pot.get(0)), e);
            }
            for(int i = 1; i < pot.size(); ++i) {
                if(!pot.get(i).sym.owner.equals(currentSymbol) && !pot.get(i).toString().startsWith("this.")) {
                    JCExpression expr1 = treeutils.makeNeqObject(Position.NOPOS, M.Ident("this." + pot.get(i)), e);
                    expr = treeutils.makeAnd(Position.NOPOS, expr, expr1);
                } else {
                    JCExpression expr1 = treeutils.makeNeqObject(Position.NOPOS, pot.get(i), e);
                    expr = treeutils.makeAnd(Position.NOPOS, expr, expr1);
                }
            }
            return expr;
        }
    }

    private boolean isSuperType(Type base, Type sup) {
        if(base.equals(sup)) return true;
        if(!(base instanceof Type.ClassType) || !(sup instanceof Type.ClassType)) {
            return false;
        }
        Type.ClassType b = (Type.ClassType)base;
        return isSuperType(b.supertype_field, sup);
    }

    public JCExpression editAssignable(JCArrayAccess e) {
        List<JmlStoreRefArrayRange> pot = List.from(currentAssignable.stream().filter(as -> as instanceof JmlStoreRefArrayRange)
                .map(arr -> ((JmlStoreRefArrayRange)arr))
                .collect(Collectors.toList()));
        JCExpression expr = editAssignable(e.indexed);
        if(pot.size() == 0) {
            return expr;
        }
        JCExpression exprs = treeutils.makeNeqObject(Position.NOPOS, pot.get(0).expression, e.indexed);
        if(pot.get(0).lo != null || pot.get(0).hi != null) {
            JCExpression hi = pot.get(0).hi;
            JCExpression lo = pot.get(0).lo;
            if(!(hi instanceof JCIdent || hi instanceof JCLiteral || lo instanceof JCIdent || lo instanceof JCLiteral)) {
                throw new RuntimeException("Only sidecondition free array indices supported. (" + e.toString() + ")");
            }
            if(hi == null) {
                hi = treeutils.makeBinary(Position.NOPOS, Tag.MINUS, treeutils.makeArrayLength(Position.NOPOS, pot.get(0).expression), M.Literal(1));
            }
            if(lo == null) {
                lo = treeutils.makeArrayLength(Position.NOPOS, M.Literal(0));
            }
            exprs = treeutils.makeOr(Position.NOPOS, exprs, treeutils.makeBinary(Position.NOPOS, Tag.GT, e.getIndex(), hi));
            exprs = treeutils.makeOr(Position.NOPOS, exprs, treeutils.makeBinary(Position.NOPOS, Tag.LT, e.getIndex(), lo));
        }
        expr = treeutils.makeAnd(Position.NOPOS, expr, exprs);
        for(int i = 1; i < pot.size(); ++i) {
            JCExpression expr1 = treeutils.makeNeqObject(Position.NOPOS, pot.get(i).expression, e.indexed);
            if(pot.get(i).lo != null || pot.get(0).hi != null) {
                JCExpression hi = pot.get(i).hi;
                JCExpression lo = pot.get(i).lo;
                if(hi == null) {
                    hi = treeutils.makeBinary(Position.NOPOS, Tag.MINUS, treeutils.makeArrayLength(Position.NOPOS, pot.get(i).expression), M.Literal(1));
                }
                if(lo == null) {
                    lo = treeutils.makeArrayLength(Position.NOPOS, M.Literal(0));
                }
                expr1 = treeutils.makeOr(Position.NOPOS, expr1, treeutils.makeBinary(Position.NOPOS, Tag.GT, e.getIndex(), hi));
                expr1 = treeutils.makeOr(Position.NOPOS, expr1, treeutils.makeBinary(Position.NOPOS, Tag.LT, e.getIndex(), lo));
            }
            expr = treeutils.makeAnd(Position.NOPOS, expr, expr1);
        }
        return expr;
    }

    public JCExpression editAssignable(JmlStoreRefArrayRange e) {
        List<JmlStoreRefArrayRange> pot = List.from(currentAssignable.stream().filter(as -> as instanceof JmlStoreRefArrayRange)
                .map(arr -> ((JmlStoreRefArrayRange)arr))
                .collect(Collectors.toList()));
        JCExpression expr = editAssignable(e.expression);
        if(pot.size() == 0) {
            return expr;
        }
        JCExpression exprs = treeutils.makeNeqObject(Position.NOPOS, pot.get(0).expression, e.expression);
        if(pot.get(0).lo != null || pot.get(0).hi != null) {
            JCExpression hi = pot.get(0).hi;
            JCExpression lo = pot.get(0).lo;
            if(hi == null) {
                hi = treeutils.makeBinary(Position.NOPOS, Tag.MINUS, treeutils.makeArrayLength(Position.NOPOS, pot.get(0).expression), M.Literal(1));
            }
            if(lo == null) {
                lo = treeutils.makeArrayLength(Position.NOPOS, M.Literal(0));
            }
            exprs = treeutils.makeOr(Position.NOPOS, exprs, treeutils.makeBinary(Position.NOPOS, Tag.GT, e.hi, hi));
            exprs = treeutils.makeOr(Position.NOPOS, exprs, treeutils.makeBinary(Position.NOPOS, Tag.LT, e.lo, lo));
        }
        expr = treeutils.makeAnd(Position.NOPOS, expr, exprs);
        for(int i = 1; i < pot.size(); ++i) {
            JCExpression expr1 = treeutils.makeNeqObject(Position.NOPOS, pot.get(i).expression, e.expression);
            if(pot.get(i).lo != null || pot.get(0).hi != null) {
                JCExpression hi = pot.get(i).hi;
                JCExpression lo = pot.get(i).lo;
                if(hi == null) {
                    hi = treeutils.makeBinary(Position.NOPOS, Tag.MINUS, treeutils.makeArrayLength(Position.NOPOS, pot.get(i).expression), M.Literal(1));
                }
                if(lo == null) {
                    lo = treeutils.makeArrayLength(Position.NOPOS, M.Literal(0));
                }
                expr1 = treeutils.makeOr(Position.NOPOS, expr1, treeutils.makeBinary(Position.NOPOS, Tag.GT, e.hi, hi));
                expr1 = treeutils.makeOr(Position.NOPOS, expr1, treeutils.makeBinary(Position.NOPOS, Tag.LT, e.lo, lo));
            }
            expr = treeutils.makeAnd(Position.NOPOS, expr, expr1);
        }
        return expr;
    }

    public JCExpression editAssignable(JCFieldAccess f) {
        List<JCFieldAccess> pot = List.from(currentAssignable.stream().filter(as -> as instanceof JCFieldAccess)
                .map(arr -> ((JCFieldAccess)arr))
                .filter(fa -> fa.name == f.name || fa.name == null)
                .collect(Collectors.toList()));
        List<JCIdent> pot1 = List.from(currentAssignable.stream().filter(as -> as instanceof JCIdent)
                .map(arr -> ((JCIdent)arr))
                .filter(i -> !i.type.isPrimitive())
                .collect(Collectors.toList()));

        JCExpression expr = null;
        if(f.name == null) {
            pot = List.from(currentAssignable.stream().filter(as -> as instanceof JCFieldAccess)
                    .map(arr -> ((JCFieldAccess)arr))
                    .filter(fa -> fa.name == null)
                    .collect(Collectors.toList()));
            if(pot.size() == 0) {
                return M.Literal(true);
            }
        }
        for(JCFieldAccess fa : pot) {
            if(expr == null) {
                expr = editAssignable(f.selected, fa.selected, true);
            } else {
                expr = treeutils.makeAnd(Position.NOPOS, expr, editAssignable(f.selected, fa.selected, true));
            }

        }
        for(JCIdent i : pot1) {
            if(expr == null) {
                expr = treeutils.makeNeqObject(Position.NOPOS, i, f);
            } else {
                expr = treeutils.makeAnd(Position.NOPOS, expr, treeutils.makeNeqObject(Position.NOPOS, i, f));
            }
        }
        if(expr == null) {
            return M.Literal(true);
        }
        return expr;
    }

    private JCExpression editAssignable(JCExpression lhs, JCExpression assignable) {
        List<JCExpression> tmp = currentAssignable;
        currentAssignable = List.of(assignable);
        JCExpression res = editAssignable(lhs, false);
        currentAssignable = tmp;
        return res;

    }

    private JCExpression editAssignable(JCExpression lhs, JCExpression assignable, boolean ignoreLocals) {
        List<JCExpression> tmp = currentAssignable;
        currentAssignable = List.of(assignable);
        JCExpression res = editAssignable(lhs, ignoreLocals);
        currentAssignable = tmp;
        return res;

    }
}
