import com.sun.source.tree.AssignmentTree;
import com.sun.source.tree.BinaryTree;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
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
import javafx.geometry.Pos;
import jdk.nashorn.internal.codegen.CompilerConstants;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.stream.Collectors;

import static com.sun.tools.javac.tree.JCTree.*;
import static org.jmlspecs.openjml.JmlTree.*;

/**
 * Created by jklamroth on 11/14/18.
 */
public class JmlExpressionVisitor extends JmlTreeCopier {
    private final Maker M;
    private final Context context;
    private final Log log;
    private final Names names;
    private final Nowarns nowarns;
    private final Symtab syms;
    private final Types types;
    private final Utils utils;
    private final JmlTypes jmltypes;
    private final JmlSpecs specs;
    private final JmlTreeUtils treeutils;
    private final translationUtils transUtils;
    private final JmlAttr attr;
    private final Name resultName;
    private final Name exceptionName;
    private final Name exceptionNameCall;
    private final Name terminationName;
    private final ClassReader reader;
    private final Symbol.ClassSymbol utilsClass;
    private final JCIdent preLabel;
    private Symbol currentSymbol;
    private int boolVarCounter = 0;
    private List<JCStatement> newStatements = List.nil();
    private Symbol returnBool = null;
    private Symbol returnVar = null;
    private VerifyFunctionVisitor.TranslationMode translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
    private Map<Integer, JCVariableDecl> oldVars = new HashMap<>();
    private  final BaseVisitor baseVisitor;
    private List<JCExpression> assertAssumptions = List.nil();
    private List<JCExpression> currentAssignable = List.nil();



    public JmlExpressionVisitor(Context context, Maker maker,
                                BaseVisitor base,
                                VerifyFunctionVisitor.TranslationMode translationMode,
                                Map<Integer, JCVariableDecl> oldVars,
                                Symbol returnVar) {
        super(context, maker);
        baseVisitor = base;
        this.context = context;
        this.log = Log.instance(context);
        this.M = Maker.instance(context);
        this.names = Names.instance(context);
        this.nowarns = Nowarns.instance(context);
        this.syms = Symtab.instance(context);
        this.types = Types.instance(context);
        this.utils = Utils.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.jmltypes = JmlTypes.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        transUtils = new translationUtils(context, M);
        this.attr = JmlAttr.instance(context);
        this.resultName = names.fromString(Strings.resultVarString);
        this.exceptionName = names.fromString(Strings.exceptionVarString);
        this.exceptionNameCall = names.fromString(Strings.exceptionCallVarString);
        this.terminationName = names.fromString(Strings.terminationVarString);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
        this.utilsClass = reader.enterClass(names.fromString(Strings.runtimeUtilsFQName));
        this.preLabel = treeutils.makeIdent(Position.NOPOS, Strings.empty, syms.intType);
        this.translationMode = translationMode;
        this.oldVars = oldVars;
        this.returnVar = returnVar;
    }

    @Override
    public JCTree visitJmlQuantifiedExpr(JmlQuantifiedExpr that, Void p) {
        returnBool = null;
        JmlQuantifiedExpr copy = that;

        if(translationMode == VerifyFunctionVisitor.TranslationMode.ENSURES) {
            if(copy.op == JmlTokenKind.BSFORALL) {
                JCVariableDecl quantVar = transUtils.makeNondetIntVar(names.fromString(that.decls.get(0).getName().toString()), currentSymbol);
                newStatements = newStatements.append(quantVar);
                assertAssumptions = assertAssumptions.append(super.copy(copy.range));
                JCExpression value = super.copy(copy.value);
                return value;
            } else if(copy.op == JmlTokenKind.BSEXISTS) {
                List<JCStatement> stmts = newStatements;
                newStatements = List.nil();
                JCExpression value = super.copy(copy.value);
                JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentSymbol, treeutils.makeLit(Position.NOPOS, syms.booleanType, false));
                JCBinary b = M.Binary(Tag.OR, M.Ident(boolVar), value);
                newStatements = newStatements.append(M.Exec(M.Assign(M.Ident(boolVar), b)));
                List<JCStatement> l = List.nil();
                l = l.append(boolVar);
                l = l.append(transUtils.makeStandardLoopFromRange(copy.range, newStatements, that.decls.get(0), currentSymbol));
                newStatements = stmts.appendList(l);
                returnBool = boolVar.sym;
                return M.Ident(boolVar);
            }
        } else if(translationMode == VerifyFunctionVisitor.TranslationMode.REQUIRES) {
            if(copy.op == JmlTokenKind.BSFORALL) {
                List<JCStatement> stmts = newStatements;
                newStatements = List.nil();
                JCExpression value = super.copy(copy.value);
                JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentSymbol, treeutils.makeLit(Position.NOPOS, syms.booleanType, true));
                JCBinary b = M.Binary(Tag.AND, M.Ident(boolVar), value);
                newStatements = newStatements.append(M.Exec(M.Assign(M.Ident(boolVar), b)));
                List<JCStatement> l = List.nil();
                l = l.append(boolVar);
                l = l.append(transUtils.makeStandardLoopFromRange(copy.range, newStatements, that.decls.get(0), currentSymbol));
                newStatements = stmts.appendList(l);
                returnBool = boolVar.sym;
                return M.Ident(boolVar);
            } else if(copy.op == JmlTokenKind.BSEXISTS) {
                JCVariableDecl quantVar = transUtils.makeNondetIntVar(names.fromString(that.decls.get(0).getName().toString()), currentSymbol);
                newStatements = newStatements.append(quantVar);
                newStatements = newStatements.append(translationUtils.makeAssumeStatement(super.copy(copy.range), M));
                JCExpression value = super.copy(copy.value);
                return value;
            }
        }
        return copy;
    }

    @Override
    public JCTree visitBinary(BinaryTree node, Void p) {
        int countStmts = newStatements.size();
        JCBinary copy = (JCBinary) super.visitBinary(node, p);
        if(copy.operator.asType().getReturnType() == syms.booleanType && countStmts < newStatements.size()) {
            JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentSymbol, copy);
            //newStatements.append(boolVar);
            returnBool = boolVar.sym;
            return copy;
        }
        return super.visitBinary(node, p);
    }

    /*@Override
    public JCTree visitLiteral(LiteralTree node, Void p) {
        JCLiteral copy = (JCLiteral) super.visitLiteral(node, p);
        if(copy.type.baseType() == syms.booleanType) {
            JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentSymbol, copy);
            newStatements = newStatements.append(boolVar);
            returnBool = boolVar.sym;
            return M.Ident(boolVar);
        }
        return super.visitLiteral(node, p);
    }*/

    @Override
    public JCTree visitJmlMethodInvocation(JmlMethodInvocation that, Void p) {
        switch (that.token) {
            case BSOLD:
                JCExpression arg = that.getArguments().get(0);
                JCVariableDecl oldVar;
                if(arg instanceof JCIdent) {
                    if(!oldVars.keySet().contains(((JCIdent) arg).sym.hashCode())) {
                        if(arg.type instanceof Type.JCPrimitiveType) {
                            oldVar = treeutils.makeVarDef(arg.type, M.Name(String.valueOf("old" + arg.hashCode())), currentSymbol, arg);
                        } else {
                            oldVar = treeutils.makeVarDef(arg.type, M.Name(String.valueOf("old" + arg.hashCode())), currentSymbol,
                                    M.Apply(List.nil(),
                                            M.Select(arg, M.Name("clone")),
                                            List.nil()));
                        }
                        oldVars.put(((JCIdent) arg).sym.hashCode(), oldVar);
                    } else {
                        oldVar = oldVars.get(((JCIdent) arg).sym.hashCode());
                    }
                } else {
                    if(arg.type instanceof Type.JCPrimitiveType) {
                        oldVar = treeutils.makeVarDef(arg.type, M.Name(String.valueOf("old" + arg.hashCode())), currentSymbol, arg);
                    } else {
                        oldVar = treeutils.makeVarDef(arg.type, M.Name(String.valueOf("old" + arg.hashCode())), currentSymbol,
                                M.Apply(List.nil(),
                                        M.Select(arg, M.Name("clone")),
                                        List.nil()));
                    }
                    oldVars.put(arg.hashCode(), oldVar);
                }

                return M.Ident(oldVar);
            default:
                throw new RuntimeException("JmlMethodInvocation with type " + that.token + " is not supported.");
        }
    }

    @Override
    public JCTree visitJmlSingleton(JmlSingleton that, Void p) {
        switch (that.token) {
            case BSRESULT:
                return M.Ident(returnVar);
            default:
                throw new RuntimeException("JmlSingleton with type " + that.token + " is not supported.");
        }
    }

    @Override
    public JCTree visitJmlStatementLoopExpr(JmlTree.JmlStatementLoopExpr that, Void p) {
        if(that.token == JmlTokenKind.LOOP_INVARIANT) {
            return super.visitJmlStatementLoopExpr(that, p);
        }
        throw new RuntimeException("Token " + that.token + " currently not supported.");
    }

    @Override
    public JCTree visitJmlForLoop(JmlTree.JmlForLoop that, Void p) {
        if(that.loopSpecs == null) {
            return super.visitJmlForLoop(that, p);
        }
        if(that.init.size() > 1) {
            throw new RuntimeException("More than 1 loopVariable currently not supported");
        }
        JCVariableDecl loopVar = null;
        if(that.init.size() > 0) {
            loopVar = (JCVariableDecl)that.init.get(0);
        }
        if(loopVar != null)  {
            newStatements = newStatements.append(loopVar);
        }
        assumeOrAssertAllInvs(that, VerifyFunctionVisitor.TranslationMode.ENSURES);
        if(loopVar != null) {
            newStatements = newStatements.append(M.Exec(M.Assign(M.Ident(loopVar), transUtils.makeNondetInt(currentSymbol))));
        }
        for(JmlTree.JmlStatementLoop spec : that.loopSpecs) {
            if (spec instanceof JmlStatementLoopModifies) {
                newStatements = newStatements.appendList(havoc(((JmlStatementLoopModifies) spec).storerefs));
            }
        }
        assumeOrAssertAllInvs(that, VerifyFunctionVisitor.TranslationMode.REQUIRES);
        List<JCStatement> statements = newStatements;
        newStatements = List.nil();
        JCStatement assumefalse = translationUtils.makeAssumeStatement(treeutils.makeLit(Position.NOPOS, syms.booleanType, false), M);
        List<JCStatement> ifbodystatements = List.nil();
        translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        for(JCStatement st : ((JCBlock)that.body).getStatements()) {
            JCStatement stcopy = super.copy(st);
            if(!(st instanceof JmlForLoop)) {
                ifbodystatements = ifbodystatements.append(stcopy);
            } else {
                ifbodystatements = ifbodystatements.appendList(newStatements);
                newStatements = List.nil();
            }
        }
        for(JCExpressionStatement est : that.step) {
            ifbodystatements = ifbodystatements.append(est);
        }
        assumeOrAssertAllInvs(that, VerifyFunctionVisitor.TranslationMode.ENSURES);
        ifbodystatements = ifbodystatements.appendList(newStatements);
        JCBlock ifbody = M.Block(0L, ifbodystatements.append(assumefalse));
        newStatements = statements.append(M.If(that.cond, ifbody, null));
        return null;
    }

    private void assumeOrAssertAllInvs(JmlForLoop that, VerifyFunctionVisitor.TranslationMode mode) {
        List<JCStatement> l = newStatements;
        newStatements = List.nil();
        for(JmlTree.JmlStatementLoop spec : that.loopSpecs) {
            if(spec instanceof JmlStatementLoopExpr) {
                translationMode = mode;
                returnBool = null;
                JCExpression assertCopy = this.copy(((JmlStatementLoopExpr) spec).expression);
                if(returnBool == null) {
                    if(mode == VerifyFunctionVisitor.TranslationMode.ENSURES) {
                        newStatements = newStatements.append(translationUtils.makeAssertStatement(assertCopy, M, assertAssumptions));
                        assertAssumptions = List.nil();
                    } else {
                        newStatements = newStatements.append(translationUtils.makeAssumeStatement(assertCopy, M));
                    }
                } else {
                    if(mode == VerifyFunctionVisitor.TranslationMode.ENSURES) {
                        newStatements = newStatements.append(translationUtils.makeAssertStatement(M.Ident(returnBool), M, assertAssumptions));
                        assertAssumptions = List.nil();
                    } else {
                        newStatements = newStatements.append(translationUtils.makeAssumeStatement(M.Ident(returnBool), M));
                    }
                }
            }
        }
        newStatements = l.append(M.Block(0L, newStatements));
    }

    private List<JCStatement> havoc(List<JCExpression> storerefs) {
        List<JCStatement> res = List.nil();
        for(JCExpression expr : storerefs) {
            if(expr instanceof JCIdent) {
                if(((JCIdent) expr).type.isPrimitive()) {
                    res = res.append(M.Exec(M.Assign(expr, getNondetFunctionForType(((JCIdent) expr).type))));
                }
            } else if(expr instanceof  JmlStoreRefArrayRange) {
                JmlStoreRefArrayRange aexpr = (JmlStoreRefArrayRange)expr;
                if(aexpr.hi == null && aexpr.lo == null) {
                    //TODO not always a valid translation
                    List<JCStatement> block = List.nil();
                    JCVariableDecl arrLength = treeutils.makeVariableDecl(M.Name("arrLength"), syms.intType, treeutils.makeArrayLength(Position.NOPOS, aexpr.expression), Position.NOPOS);
                    block = block.append(arrLength);
                    block = block.append(M.Exec(M.Assign(aexpr.expression, transUtils.makeNondetWithoutNull(currentSymbol))));
                    JCExpression assumeLength = treeutils.makeEquality(Position.NOPOS, treeutils.makeArrayLength(Position.NOPOS, aexpr.expression), M.Ident(arrLength));
                    block = block.append(translationUtils.makeAssumeStatement(assumeLength, M));
                    res = res.append(M.Block(0l, block));
                } else if(aexpr.hi != null && aexpr.lo.toString().equals(aexpr.hi.toString())) {
                    Type elemtype = ((Type.ArrayType)aexpr.expression.type).elemtype;
                    JCExpression elemExpr = M.Indexed(aexpr.expression, aexpr.lo);
                    if(elemtype.isPrimitive()) {
                        res = res.append(M.Exec(M.Assign(elemExpr, getNondetFunctionForType(elemtype))));
                    } else {
                        res = res.append(M.Exec(M.Assign(elemExpr, transUtils.makeNondetWithNull(currentSymbol))));
                    }
                } else {
                    try {
                        JCVariableDecl loopVar = treeutils.makeIntVarDef(M.Name("__tmpVar__"), aexpr.lo, currentSymbol);
                        JCExpression range = treeutils.makeBinary(Position.NOPOS, Tag.LE, M.Ident(loopVar), aexpr.hi);
                        JCExpression elemExpr = M.Indexed(aexpr.expression, M.Ident(loopVar));
                        Type elemtype = ((Type.ArrayType)aexpr.expression.type).elemtype;
                        List<JCStatement> body = List.of(M.Exec(M.Assign(elemExpr, getNondetFunctionForType(elemtype))));
                        res = res.append(transUtils.makeStandardLoop(range, body, loopVar, currentSymbol));
                    } catch (NumberFormatException e) {
                        throw new NotImplementedException();
                    }
                }
            } else {
                throw new NotImplementedException();
            }
        }
        return res;
    }

    private JCMethodInvocation getNondetFunctionForType(Type type) {
        if(type.equals(syms.intType)) {
            return transUtils.makeNondetInt(currentSymbol);
        } else if(type.equals(syms.floatType)) {
            return transUtils.makeNondetFloat(currentSymbol);
        } else if(type.equals(syms.doubleType)) {
            return transUtils.makeNondetDouble(currentSymbol);
        } else if(type.equals(syms.longType)) {
            return transUtils.makeNondetLong(currentSymbol);
        } else if(type.equals(syms.shortType)) {
            return transUtils.makeNondetShort(currentSymbol);
        } else if(type.equals(syms.charType)) {
            return transUtils.makeNondetChar(currentSymbol);
        }
        throw new NotImplementedException();
    }

    @Override
    public JCTree visitAssignment(AssignmentTree node, Void p) {
        JCAssign assign = (JCAssign) node;
        JCExpression cond = null;
        if(assign.getVariable() instanceof JCIdent) {
            cond = editAssignable((JCIdent)assign.getVariable());
        } else if(assign.getVariable() instanceof JCArrayAccess) {
            cond = editAssignable((JCArrayAccess) assign.getVariable());
        } else if(assign.getVariable() instanceof JCFieldAccess) {
            cond = editAssignable((JCFieldAccess) assign.getVariable());
        } else {
            new Exception("Could not handle assignment " + node.toString());
        }
        if(cond != null) {
            JCIf ifst = M.If(cond, makeAssignmentException("Illegal assignment: " + assign.toString()), null);
            newStatements = newStatements.append(ifst);
        }
        newStatements = newStatements.append(M.Exec(assign));
        return null;
    }

    public JCExpression editAssignable(JCIdent e) {
        JCIdent lhs = e;
        if(lhs.type.isPrimitive()) {
            if(!currentAssignable.stream().filter(as -> as instanceof JCIdent)
                    .anyMatch(as -> ((JCIdent)as).sym.equals(lhs.sym))) {
                return M.Literal(true);
            }
            return null;
        } else {
            List<JCExpression> pot = List.from(currentAssignable.stream().filter(as -> as instanceof JCIdent)
                    .filter(as -> !((JCIdent)as).type.isPrimitive())
                    .collect(Collectors.toList()));
            if(pot.size() == 0) {
                return M.Literal(true);
            }
            JCExpression expr = treeutils.makeNeqObject(Position.NOPOS, pot.get(0), lhs);
            for(int i = 1; i < pot.size(); ++i) {
                expr = treeutils.makeAnd(Position.NOPOS, expr, treeutils.makeNeqObject(Position.NOPOS, pot.get(i), lhs));
            }
            return expr;
        }
    }

    public JCThrow makeAssignmentException(String msg) {
        JCExpression ty = M.Type(syms.runtimeExceptionType);
        JCTree.JCExpression msgexpr = treeutils.makeStringLiteral(Position.NOPOS, msg);
        JCThrow throwStmt = M.Throw(M.NewClass(null, null, ty, List.of(msgexpr), null));
        return throwStmt;
    }

    public JCExpression editAssignable(JCArrayAccess e) {
        JCArrayAccess lhs = e;
        List<JmlStoreRefArrayRange> pot = List.from(currentAssignable.stream().filter(as -> as instanceof JmlStoreRefArrayRange)
                .map(arr -> ((JmlStoreRefArrayRange)arr))
                .collect(Collectors.toList()));
        if(pot.size() == 0) {
            return M.Literal(true);
        }
        JCExpression expr = treeutils.makeNeqObject(Position.NOPOS, pot.get(0).expression, lhs.indexed);
        if(pot.get(0).lo != null || pot.get(0).hi != null) {
            JCExpression hi = pot.get(0).hi;
            JCExpression lo = pot.get(0).lo;
            if(hi == null) {
                hi = treeutils.makeArrayLength(Position.NOPOS, pot.get(0).expression);
            }
            if(lo == null) {
                lo = treeutils.makeArrayLength(Position.NOPOS, M.Literal(0));
            }
            expr = treeutils.makeOr(Position.NOPOS, expr, treeutils.makeBinary(Position.NOPOS, Tag.GT, lhs.getIndex(), hi));
            expr = treeutils.makeOr(Position.NOPOS, expr, treeutils.makeBinary(Position.NOPOS, Tag.LT, lhs.getIndex(), lo));
        }
        for(int i = 1; i < pot.size(); ++i) {
            JCExpression expr1 = treeutils.makeNeqObject(Position.NOPOS, pot.get(i).expression, lhs.indexed);
            if(pot.get(i).lo != null || pot.get(0).hi != null) {
                JCExpression hi = pot.get(i).hi;
                JCExpression lo = pot.get(i).lo;
                if(hi == null) {
                    hi = treeutils.makeArrayLength(Position.NOPOS, pot.get(i).expression);
                }
                if(lo == null) {
                    lo = treeutils.makeArrayLength(Position.NOPOS, M.Literal(0));
                }
                expr1 = treeutils.makeOr(Position.NOPOS, expr1, treeutils.makeBinary(Position.NOPOS, Tag.LE, lhs.getIndex(), hi));
                expr1 = treeutils.makeOr(Position.NOPOS, expr1, treeutils.makeBinary(Position.NOPOS, Tag.GE, lhs.getIndex(), lo));
            }
            expr = treeutils.makeAnd(Position.NOPOS, expr, expr1);
        }
        return expr;
    }

    public JCExpression editAssignable(JCFieldAccess f) {
        JCFieldAccess lhs = f;
        List<JCFieldAccess> pot = List.from(currentAssignable.stream().filter(as -> as instanceof JCFieldAccess)
                .map(arr -> ((JCFieldAccess)arr))
                .collect(Collectors.toList()));
        JCExpression selected = lhs.selected;
        LinkedList<JCFieldAccess> accessList = new LinkedList();
        while(selected instanceof JCFieldAccess) {
            accessList.addFirst((JCFieldAccess) selected);
            selected = ((JCFieldAccess) selected).selected;
        }
        JCExpression expr = null;
        for(JCFieldAccess fa : pot) {
            JCExpression selected1 = fa.selected;
            LinkedList<JCFieldAccess> accessList1 = new LinkedList();
            while(selected1 instanceof JCFieldAccess) {
                accessList1.addFirst((JCFieldAccess) selected1);
                selected1 = ((JCFieldAccess) selected1).selected;
            }
            boolean valid = true;
            while (accessList1.size() > 0){
                if(accessList.size() > 0) {
                    if (!accessList1.get(0).equals(accessList.get(0))) {
                        valid = false;
                    } else {
                        accessList.remove(0);
                        accessList1.remove(0);
                    }
                } else {
                    valid = false;
                }
            }
            if(valid && (lhs.name.equals(fa.name) || fa.name == null || (accessList.size() > 0 && accessList.getFirst().name.equals(fa.name)))) {
                if(expr == null) {
                    expr = treeutils.makeNeqObject(Position.NOPOS, selected, selected1);
                } else {
                    expr = treeutils.makeAnd(Position.NOPOS, expr, treeutils.makeNeqObject(Position.NOPOS, selected, selected1));
                }
            }
        }
        if(expr == null) {
            return M.Literal(true);
        } else {
            return expr;
        }
    }

    public List<JCStatement> getNewStatements() {
        return newStatements;
    }

    public Symbol getReturnBool() {
        return returnBool;
    }

    public Map<Integer, JCVariableDecl> getOldVars() {
        return oldVars;
    }

    public List<JCExpression> getAssertionAssumptions() { return assertAssumptions; }

    public void setCurrentAssignable(List<JCExpression> currentAssignable) {
        this.currentAssignable = currentAssignable;
    }
}