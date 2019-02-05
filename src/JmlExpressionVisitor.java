import com.sun.source.tree.AssignmentTree;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.BreakTree;
import com.sun.source.tree.CaseTree;
import com.sun.source.tree.CompoundAssignmentTree;
import com.sun.source.tree.ContinueTree;
import com.sun.source.tree.ExpressionStatementTree;
import com.sun.source.tree.IfTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.ReturnTree;
import com.sun.source.tree.SwitchTree;
import com.sun.source.tree.ThrowTree;
import com.sun.source.tree.TryTree;
import com.sun.source.tree.UnaryTree;
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
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;

import java.util.ArrayList;
import java.util.HashMap;
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
    private final TranslationUtils transUtils;


    private final JmlAttr attr;
    private final Name resultName;
    private final Name exceptionName;
    private final Name exceptionNameCall;
    private final Name terminationName;
    private final ClassReader reader;
    private final Symbol.ClassSymbol utilsClass;
    private final JCIdent preLabel;
    private Symbol currentSymbol;
    private JmlMethodDecl currentMethod;
    private int boolVarCounter = 0;
    private List<JCStatement> newStatements = List.nil();
    private Symbol returnVar = null;
    private VerifyFunctionVisitor.TranslationMode translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
    private Map<Integer, JCVariableDecl> oldVars = new HashMap<>();
    private  final BaseVisitor baseVisitor;
    private JCIf innermostIf = null;
    private List<JCExpression> currentAssignable = List.nil();
    private List<JCStatement> combinedNewReqStatements = List.nil();
    private List<JCStatement> combinedNewEnsStatements = List.nil();
    private List<Tag> supportedBinaryTags = List.of(Tag.PLUS, Tag.MINUS, Tag.MUL, Tag.DIV, Tag.MOD,
            Tag.BITXOR, Tag.BITOR, Tag.BITAND, Tag.SL, Tag.SR, Tag.AND, Tag.OR, Tag.EQ, Tag.NE,
            Tag.GE, Tag.GT, Tag.LE, Tag.LT);



    public JmlExpressionVisitor(Context context, Maker maker,
                                BaseVisitor base,
                                VerifyFunctionVisitor.TranslationMode translationMode,
                                Map<Integer, JCVariableDecl> oldVars,
                                Symbol returnVar,
                                JmlMethodDecl currentMethod) {
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
        transUtils = new TranslationUtils(context, M);
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
        this.currentSymbol = currentMethod.sym;
        this.currentMethod = currentMethod;
    }

    @Override
    public JCTree visitExpressionStatement(ExpressionStatementTree node, Void p) {
        JCExpression copy = super.copy((JCExpression)(node.getExpression()));
        if(newStatements.size() > 0) {
            newStatements = newStatements.append(M.Exec(copy));
        }
        return M.Exec(copy);
    }

    @Override
    public JCTree visitJmlStatementExpr(JmlStatementExpr that, Void p) {
        JCExpression copy = null;
        if(that.token == JmlTokenKind.ASSERT) {
            translationMode = VerifyFunctionVisitor.TranslationMode.ASSERT;
            JCExpression expr = transUtils.unwrapExpression(that.expression);
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            copy = super.copy(expr, p);
            newStatements = newStatements.appendList(transUtils.assumeOrAssertInIf(innermostIf, copy, translationMode));
            innermostIf = null;
            newStatements = tmp.append(M.Block(0L, newStatements));
            translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        } else if(that.token == JmlTokenKind.ASSUME) {
            translationMode = VerifyFunctionVisitor.TranslationMode.ASSUME;
            JCExpression expr = transUtils.unwrapExpression(that.expression);
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            copy = super.copy(expr, p);
            newStatements = newStatements.appendList(transUtils.assumeOrAssertInIf(innermostIf, copy, translationMode));
            innermostIf = null;
            newStatements = tmp.append(M.Block(0L, newStatements));
            translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        } else {
            throw new RuntimeException("Token of kind " + that.token + " not supported.");
        }
        return M.JmlExpressionStatement(that.token, that.label, copy);
    }

    @Override
    public JCTree visitUnary(UnaryTree node, Void p) {
        JCUnary u = (JCUnary)node;
        if(u.getTag() == Tag.NOT) {
            return super.visitUnary(node, p);
        } else if(u.getTag() == Tag.POSTINC || u.getTag() == Tag.POSTDEC ||
                u.getTag() == Tag.PREDEC || u.getTag() == Tag.PREINC) {
            if(currentAssignable.stream().anyMatch(loc -> loc instanceof JmlStoreRefKeyword)) {
                return super.visitUnary(node, p);
            }
            JCExpression cond = editAssignable(u.arg);
            if(cond != null) {
                JCIf ifst = M.If(cond, makeException("Illegal assignment: " + u.toString()), null);
                newStatements = newStatements.append(ifst);
                //newStatements = newStatements.append(M.Exec(u));
            }
            return super.visitUnary(node, p);
        } else {
            throw new RuntimeException("Unsupported unary token: " + u.getTag());
        }
    }

    @Override
    public JCTree visitJmlQuantifiedExpr(JmlQuantifiedExpr that, Void p) {
        JmlQuantifiedExpr copy = (JmlQuantifiedExpr)that.clone();

        if(translationMode == VerifyFunctionVisitor.TranslationMode.ASSERT) {
            if(copy.op == JmlTokenKind.BSFORALL) {
                JCVariableDecl quantVar = transUtils.makeNondetIntVar(names.fromString(that.decls.get(0).getName().toString()), currentSymbol);
                newStatements = newStatements.append(quantVar);
                JCExpression cond = super.copy(copy.range);
                JCExpression value = super.copy(copy.value);
                JCExpression res = treeutils.makeOr(Position.NOPOS, treeutils.makeNot(Position.NOPOS, cond), value);
                return res;
            } else if(copy.op == JmlTokenKind.BSEXISTS) {
                List<JCStatement> stmts = newStatements;
                newStatements = List.nil();
                JCExpression value = super.copy(copy.value);
                JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentSymbol, treeutils.makeLit(Position.NOPOS, syms.booleanType, false));
                JCBinary b = M.Binary(Tag.OR, M.Ident(boolVar), value);
                newStatements = newStatements.append(M.Exec(M.Assign(M.Ident(boolVar), b)));
                List<JCStatement> l = List.nil();
                l = l.append(boolVar);
                l = l.append(transUtils.makeStandardLoopFromRange(super.copy(copy.range), newStatements, that.decls.get(0), currentSymbol));
                newStatements = stmts.appendList(l);
                return M.Ident(boolVar);
            } else {
                throw new RuntimeException("Unkown token tpye in quantified Expression: " + copy.op);
            }
        } else if(translationMode == VerifyFunctionVisitor.TranslationMode.ASSUME) {
            if(copy.op == JmlTokenKind.BSFORALL) {
                List<JCStatement> stmts = newStatements;
                newStatements = List.nil();
                innermostIf = null;
                JCExpression value = super.copy(copy.value);
                JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentSymbol, treeutils.makeLit(Position.NOPOS, syms.booleanType, true));
                JCBinary b = M.Binary(Tag.AND, M.Ident(boolVar), value);
                newStatements = newStatements.append(M.Exec(M.Assign(M.Ident(boolVar), b)));
                List<JCStatement> l = List.nil();
                l = l.append(boolVar);
                l = l.append(transUtils.makeStandardLoopFromRange(super.copy(copy.range), newStatements, that.decls.get(0), currentSymbol));
                newStatements = stmts.appendList(l);
                return M.Ident(boolVar);
            } else if(copy.op == JmlTokenKind.BSEXISTS) {
                JCVariableDecl quantVar = transUtils.makeNondetIntVar(names.fromString(that.decls.get(0).getName().toString()), currentSymbol);
                newStatements = newStatements.append(quantVar);
                JCExpression cond = super.copy(copy.range);
                JCExpression value = super.copy(copy.value);
                newStatements = newStatements.append(TranslationUtils.makeAssumeStatement(cond, M));
                return value;
            } else {
                throw new RuntimeException("Unkown token type in quantified Expression: " + copy.op);
            }
        }
        return copy;
    }

    @Override
    public JCTree visitThrow(ThrowTree node, Void p) {
        throw new RuntimeException("Throwing exceptions is currently not supported.");
    }

    @Override
    public JCTree visitJmlBinary(JmlBinary that, Void p) {
        if(that.op == JmlTokenKind.IMPLIES) {
            JCExpression rhs = super.copy(that.rhs);

            JCExpression orig = that.lhs;
            JCExpression lhs = super.copy(that.lhs);
            orig = transUtils.unwrapExpression(orig);
            if(!(orig instanceof JmlQuantifiedExpr)) {
                return treeutils.makeBinary(Position.NOPOS, Tag.OR, treeutils.makeNot(Position.NOPOS, lhs), rhs);
            } else {
                return treeutils.makeBinary(Position.NOPOS, Tag.OR, lhs, rhs);
            }
        }
        if(that.op == JmlTokenKind.EQUIVALENCE) {
            JCExpression rhs = super.copy(that.rhs);
            JCExpression lhs = super.copy(that.lhs);
            return treeutils.makeBinary(Position.NOPOS, Tag.EQ, lhs, rhs);
        }
        return super.visitJmlBinary(that, p);
    }

//    @Override
//    public JCTree visitBinary(BinaryTree node, Void p) {
//        JCBinary b = (JCBinary)node;
//        if(!supportedBinaryTags.contains(b.getTag())) {
//            throw new RuntimeException("Unsupported Operation: " + b.toString());
//        }
//        JCExpression lhs = super.copy(b.getLeftOperand());
//        JCExpression rhs = super.copy(b.getRightOperand());
//        JCBinary r = M.Binary(((JCBinary) node).getTag(), lhs, rhs);
//        r.operator = b.operator;
//        return r;
//    }

    @Override
    public JCTree visitBinary(BinaryTree node, Void p) {
        if(!supportedBinaryTags.contains(((JCBinary)node).getTag())) {
            throw new RuntimeException("Unsupported Operation: " + ((JCBinary)node).toString());
        }
        JCBinary copy = (JCBinary) super.visitBinary(node, p);
        return copy;
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
                            oldVar = treeutils.makeVarDef(arg.type, M.Name(String.valueOf("old" + oldVars.size())), currentSymbol, arg);
                        } else {
                            throw new RuntimeException("\\old of non primitive types currently not supported.");
                        }
                        oldVars.put(((JCIdent) arg).sym.hashCode(), oldVar);
                    } else {
                        oldVar = oldVars.get(((JCIdent) arg).sym.hashCode());
                    }
                } else {
                    if(arg.type instanceof Type.JCPrimitiveType) {
                        oldVar = treeutils.makeVarDef(arg.type, M.Name(String.valueOf("old" + oldVars.size())), currentSymbol, arg);
                    } else {
                        throw new RuntimeException("\\old of non primitive types currently not supported.");
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
        } else if(that.token == JmlTokenKind.DECREASES) {
            return super.visitJmlStatementLoopExpr(that, p);
        }
        throw new RuntimeException("Token " + that.token + " for loop specifications currently not supported.");
    }

    @Override
    public JCTree visitSwitch(SwitchTree node, Void p) {
        throw new RuntimeException("Switch-Statements are currently not supported.");
    }

    @Override
    public JCTree visitTry(TryTree node, Void p) {
        throw new RuntimeException("Try-Catch-Statements are currently not supported.");
    }

    @Override
    public JCTree visitCase(CaseTree node, Void p) {
        throw new RuntimeException("Case-Statements are currently not supported.");
    }

    @Override
    public JCTree visitBreak(BreakTree node, Void p) {
        throw new RuntimeException("Break-Statements are currently not supported.");
    }

    @Override
    public JCTree visitContinue(ContinueTree node, Void p) {
        throw new RuntimeException("Continue-Statements are currently not supported.");
    }

    @Override
    public JCTree visitJmlWhileLoop(JmlWhileLoop that, Void p) {
        if(that.loopSpecs == null) {
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            JmlWhileLoop copy = (JmlWhileLoop)super.visitJmlWhileLoop(that, p);
            assert(newStatements.size() == 1);
            copy.body = newStatements.get(0);
            newStatements = tmp.append(copy);
            return copy;
        }
        assumeOrAssertAllInvs(that.loopSpecs, VerifyFunctionVisitor.TranslationMode.ASSERT);
        for(JmlTree.JmlStatementLoop spec : that.loopSpecs) {
            if (spec instanceof JmlStatementLoopModifies) {
                newStatements = newStatements.appendList(transUtils.havoc(((JmlStatementLoopModifies) spec).storerefs, currentSymbol));
            }
        }
        assumeOrAssertAllInvs(that.loopSpecs, VerifyFunctionVisitor.TranslationMode.ASSUME);
        JCVariableDecl oldD = null;
        JCExpression dExpr = null;
        for(JmlStatementLoop spec : that.loopSpecs) {
            if(spec instanceof JmlStatementLoopExpr && spec.token == JmlTokenKind.DECREASES) {
                if(oldD != null) {
                    throw new RuntimeException("Only 1 decreases clause per loop allowed but found more.");
                }
                dExpr = ((JmlStatementLoopExpr) spec).expression;
                oldD = treeutils.makeIntVarDef(M.Name("oldDecreasesClauseValue"),  dExpr, currentSymbol);
                newStatements = newStatements.append(oldD);
            }
        }

        List<JCStatement> statements = newStatements;
        newStatements = List.nil();
        JCStatement assumefalse = TranslationUtils.makeAssumeStatement(treeutils.makeLit(Position.NOPOS, syms.booleanType, false), M);
        List<JCStatement> ifbodystatements = List.nil();
        translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        for(JCStatement st : ((JCBlock)that.body).getStatements()) {
            JCStatement stcopy = super.copy(st);
            if(newStatements.size() == 0) {
                ifbodystatements = ifbodystatements.append(stcopy);
            } else {
                ifbodystatements = ifbodystatements.appendList(newStatements);
                newStatements = List.nil();
            }
        }
        assumeOrAssertAllInvs(that.loopSpecs, VerifyFunctionVisitor.TranslationMode.ASSERT);
        ifbodystatements = ifbodystatements.appendList(newStatements);
        if(dExpr != null) {
            ifbodystatements = ifbodystatements.append(
                    TranslationUtils.makeAssertStatement(makeDereasesStatement(oldD, dExpr), M));
        }
        JCBlock ifbody = M.Block(0L, ifbodystatements.append(assumefalse));
        newStatements = statements.append(M.If(that.cond, ifbody, null));
        return that;
    }

    @Override
    public JCTree visitJmlDoWhileLoop(JmlDoWhileLoop that, Void p) {
        if(that.loopSpecs == null) {
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            JmlDoWhileLoop copy = (JmlDoWhileLoop)super.visitJmlDoWhileLoop(that, p);
            assert(newStatements.size() == 1);
            copy.body = newStatements.get(0);
            newStatements = tmp.append(copy);
            return copy;
        }
        throw new RuntimeException("While-Loops with invariants currently not supported.");
    }

    @Override
    public JCTree visitJmlForLoop(JmlTree.JmlForLoop that, Void p) {
        if(that.loopSpecs == null) {
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            ArrayList<JCStatement> inits = new ArrayList();
            that.init.stream().forEach(el -> inits.add(super.copy(el)));
            ArrayList<JCExpressionStatement> steps = new ArrayList();
            that.step.stream().forEach(el -> steps.add(super.copy(el)));
            newStatements = transUtils.diff(newStatements, List.from(steps));
            newStatements = transUtils.diff(newStatements, List.from(inits));
            tmp = tmp.appendList(newStatements);
            newStatements = List.nil();
            JCStatement bodyCopy = (JCStatement)super.copy(that.body);
            assert(newStatements.size() == 1);
            JmlForLoop copy = M.ForLoop(List.from(inits), super.copy(that.cond), List.from(steps), newStatements.get(0));
            newStatements = tmp.append(copy);
            return copy;
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
        assumeOrAssertAllInvs(that.loopSpecs, VerifyFunctionVisitor.TranslationMode.ASSERT);
        if(loopVar != null) {
            newStatements = newStatements.append(M.Exec(M.Assign(M.Ident(loopVar), transUtils.makeNondetInt(currentSymbol))));
        }
        for(JmlTree.JmlStatementLoop spec : that.loopSpecs) {
            if (spec instanceof JmlStatementLoopModifies) {
                newStatements = newStatements.appendList(transUtils.havoc(((JmlStatementLoopModifies) spec).storerefs, currentSymbol));
            }
        }
        assumeOrAssertAllInvs(that.loopSpecs, VerifyFunctionVisitor.TranslationMode.ASSUME);
        JCVariableDecl oldD = null;
        JCExpression dExpr = null;
        for(JmlStatementLoop spec : that.loopSpecs) {
            if(spec instanceof JmlStatementLoopExpr && spec.token == JmlTokenKind.DECREASES) {
                if(oldD != null) {
                    throw new RuntimeException("Only 1 decreases clause per loop allowed but found more.");
                }
                dExpr = ((JmlStatementLoopExpr) spec).expression;
                oldD = treeutils.makeIntVarDef(M.Name("oldDecreasesClauseValue"),  dExpr, currentSymbol);
                newStatements = newStatements.append(oldD);
            }
        }

        List<JCStatement> statements = newStatements;
        newStatements = List.nil();
        JCStatement assumefalse = TranslationUtils.makeAssumeStatement(treeutils.makeLit(Position.NOPOS, syms.booleanType, false), M);
        List<JCStatement> ifbodystatements = List.nil();
        translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        for(JCStatement st : ((JCBlock)that.body).getStatements()) {
            JCStatement stcopy = super.copy(st);
            if(newStatements.size() == 0) {
                ifbodystatements = ifbodystatements.append(stcopy);
            } else {
                ifbodystatements = ifbodystatements.appendList(newStatements);
                newStatements = List.nil();
            }
        }
        for(JCExpressionStatement est : that.step) {
            ifbodystatements = ifbodystatements.append(est);
        }
        assumeOrAssertAllInvs(that.loopSpecs, VerifyFunctionVisitor.TranslationMode.ASSERT);
        ifbodystatements = ifbodystatements.appendList(newStatements);
        if(dExpr != null) {
            ifbodystatements = ifbodystatements.append(
                    TranslationUtils.makeAssertStatement(makeDereasesStatement(oldD, dExpr), M));
        }
        JCBlock ifbody = M.Block(0L, ifbodystatements.append(assumefalse));
        newStatements = statements.append(M.If(that.cond, ifbody, null));
        return that;
    }

    private JCExpression makeDereasesStatement(JCVariableDecl oldD, JCExpression dExpr) {
        JCExpression res = M.Binary(Tag.GT, dExpr, M.Literal(0));
        JCExpression snd = M.Binary(Tag.LT, dExpr, M.Ident(oldD.name));
        return M.Binary(Tag.AND, res, snd);
    }

    @Override
    public JCTree visitReturn(ReturnTree node, Void p) {
        JCExpression expressionCopy = super.copy((JCExpression) node.getExpression(), p);
        JCAssign assign = null;
        if(returnVar != null) {
            assign = M.Assign(M.Ident(returnVar), expressionCopy);
        }
        JCExpression ty = M.Type(baseVisitor.getExceptionClass().type);
        JCThrow throwStmt = M.Throw(M.NewClass(null, null, ty, List.nil(), null));
        if(assign != null) {
            JCBlock block = M.Block(0L, List.of(M.Exec(assign), throwStmt));
            if(newStatements.size() == 0) {
                return block;
            } else {
                newStatements = newStatements.append(block);
                return block;
            }
        } else {
            JCBlock block = M.Block(0L, List.of(throwStmt));
            if(newStatements.size() == 0) {
                return block;
            } else {
                newStatements = newStatements.append(block);
                return block;
            }
        }
    }

    private void assumeOrAssertAllInvs(List<JmlStatementLoop> invs, VerifyFunctionVisitor.TranslationMode mode) {
        List<JCStatement> l = newStatements;
        newStatements = List.nil();
        VerifyFunctionVisitor.TranslationMode oldMode = translationMode;
        for(JmlTree.JmlStatementLoop spec : invs) {
            if(spec instanceof JmlStatementLoopExpr && spec.token == JmlTokenKind.LOOP_INVARIANT) {
                translationMode = mode;
                JCExpression assertCopy = this.copy(((JmlStatementLoopExpr) spec).expression);
                newStatements = newStatements.appendList(transUtils.assumeOrAssertInIf(innermostIf, assertCopy, mode));
                innermostIf = null;
            }
        }
        if(newStatements.size() > 0) {
            newStatements = l.append(M.Block(0L, newStatements));
        }
        translationMode = oldMode;
    }


    @Override
    public JCTree visitAssignment(AssignmentTree node, Void p) {
        JCAssign assign = (JCAssign) node;
        JCExpression cond = editAssignable(assign.getVariable());
        if(currentAssignable.stream().anyMatch(loc -> loc instanceof JmlStoreRefKeyword)) {
            return super.visitAssignment(node, p);
        }
        if(cond != null) {
            cond = treeutils.makeNot(Position.NOPOS, cond);
            JCStatement expr = TranslationUtils.makeAssertStatement(cond, M);
            newStatements = newStatements.append(expr);
            //newStatements = newStatements.append(M.Exec(assign));
        }
        return super.visitAssignment(node, p);
    }

    @Override
    public JCTree visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
        JCAssignOp copy = (JCAssignOp)super.visitCompoundAssignment(node, p);
        if(copy.getTag() == Tag.PLUS_ASG || copy.getTag() == Tag.MINUS_ASG) {
            if(currentAssignable.stream().anyMatch(loc -> loc instanceof JmlStoreRefKeyword)) {
                return copy;
            }
            JCExpression cond = editAssignable(copy.lhs);
            if(cond != null) {
                JCStatement assertSt = transUtils.makeAssumeOrAssertStatement(treeutils.makeNot(Position.NOPOS, cond), VerifyFunctionVisitor.TranslationMode.ASSERT);
                newStatements = newStatements.append(assertSt);
                //newStatements = newStatements.append(M.Exec(u));
            }
            return copy;
        } else {
            throw new RuntimeException("Unkonwn assignment type " + copy.toString());
        }
    }



    public JCThrow makeException(String msg) {
        JCExpression ty = M.Type(syms.runtimeExceptionType);
        JCTree.JCExpression msgexpr = treeutils.makeStringLiteral(Position.NOPOS, msg);
        JCThrow throwStmt = M.Throw(M.NewClass(null, null, ty, List.of(msgexpr), null));
        return throwStmt;
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
                return M.Literal(!currentAssignable.stream().anyMatch(loc -> loc instanceof JmlStoreRefKeyword));
            } else {
                throw new RuntimeException("Cannot handle assignment to " + e.toString());
            }
        } else {
            throw new RuntimeException("Could not handle assignment to " + e.toString());
        }
    }

    public JCExpression editAssignable(JCIdent e) {
        JCIdent lhs = e;
        if(lhs.type.isPrimitive()) {
            if(!currentAssignable.stream().filter(as -> as instanceof JCIdent)
                    .anyMatch(as -> ((JCIdent)as).sym.equals(lhs.sym))) {
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
                    .filter(as -> isSuperType(as.type , lhs.type) || isSuperType(lhs.type , as.type))
                    .collect(Collectors.toList()));
            if(pot.size() == 0) {
                return M.Literal(true);
            }
            JCExpression expr = treeutils.makeNeqObject(Position.NOPOS, pot.get(0), lhs);
            if(!pot.get(0).sym.owner.equals(currentSymbol) && !pot.get(0).toString().startsWith("this.")) {
                expr = treeutils.makeNeqObject(Position.NOPOS, M.Ident("this." + pot.get(0)), lhs);
            }
            for(int i = 1; i < pot.size(); ++i) {
                if(!pot.get(i).sym.owner.equals(currentSymbol) && !pot.get(i).toString().startsWith("this.")) {
                    JCExpression expr1 = treeutils.makeNeqObject(Position.NOPOS, M.Ident("this." + pot.get(i)), lhs);
                    expr = treeutils.makeAnd(Position.NOPOS, expr, expr1);
                } else {
                    JCExpression expr1 = treeutils.makeNeqObject(Position.NOPOS, pot.get(i), lhs);
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
        JCArrayAccess lhs = e;
        List<JmlStoreRefArrayRange> pot = List.from(currentAssignable.stream().filter(as -> as instanceof JmlStoreRefArrayRange)
                .map(arr -> ((JmlStoreRefArrayRange)arr))
                .collect(Collectors.toList()));
        JCExpression expr = editAssignable(lhs.indexed);
        if(pot.size() == 0) {
            return expr;
        }
        JCExpression exprs = treeutils.makeNeqObject(Position.NOPOS, pot.get(0).expression, lhs.indexed);
        if(pot.get(0).lo != null || pot.get(0).hi != null) {
            JCExpression hi = pot.get(0).hi;
            JCExpression lo = pot.get(0).lo;
            if(hi == null) {
                hi = treeutils.makeBinary(Position.NOPOS, Tag.MINUS, treeutils.makeArrayLength(Position.NOPOS, pot.get(0).expression), M.Literal(1));
            }
            if(lo == null) {
                lo = treeutils.makeArrayLength(Position.NOPOS, M.Literal(0));
            }
            exprs = treeutils.makeOr(Position.NOPOS, exprs, treeutils.makeBinary(Position.NOPOS, Tag.GT, lhs.getIndex(), hi));
            exprs = treeutils.makeOr(Position.NOPOS, exprs, treeutils.makeBinary(Position.NOPOS, Tag.LT, lhs.getIndex(), lo));
        }
        expr = treeutils.makeAnd(Position.NOPOS, expr, exprs);
        for(int i = 1; i < pot.size(); ++i) {
            JCExpression expr1 = treeutils.makeNeqObject(Position.NOPOS, pot.get(i).expression, lhs.indexed);
            if(pot.get(i).lo != null || pot.get(0).hi != null) {
                JCExpression hi = pot.get(i).hi;
                JCExpression lo = pot.get(i).lo;
                if(hi == null) {
                    hi = treeutils.makeBinary(Position.NOPOS, Tag.MINUS, treeutils.makeArrayLength(Position.NOPOS, pot.get(i).expression), M.Literal(1));
                }
                if(lo == null) {
                    lo = treeutils.makeArrayLength(Position.NOPOS, M.Literal(0));
                }
                expr1 = treeutils.makeOr(Position.NOPOS, expr1, treeutils.makeBinary(Position.NOPOS, Tag.GT, lhs.getIndex(), hi));
                expr1 = treeutils.makeOr(Position.NOPOS, expr1, treeutils.makeBinary(Position.NOPOS, Tag.LT, lhs.getIndex(), lo));
            }
            expr = treeutils.makeAnd(Position.NOPOS, expr, expr1);
        }
        return expr;
    }

    public JCExpression editAssignable(JmlStoreRefArrayRange e) {
        JmlStoreRefArrayRange lhs = e;
        List<JmlStoreRefArrayRange> pot = List.from(currentAssignable.stream().filter(as -> as instanceof JmlStoreRefArrayRange)
                .map(arr -> ((JmlStoreRefArrayRange)arr))
                .collect(Collectors.toList()));
        JCExpression expr = editAssignable(lhs.expression);
        if(pot.size() == 0) {
            return expr;
        }
        JCExpression exprs = treeutils.makeNeqObject(Position.NOPOS, pot.get(0).expression, lhs.expression);
        if(pot.get(0).lo != null || pot.get(0).hi != null) {
            JCExpression hi = pot.get(0).hi;
            JCExpression lo = pot.get(0).lo;
            if(hi == null) {
                hi = treeutils.makeBinary(Position.NOPOS, Tag.MINUS, treeutils.makeArrayLength(Position.NOPOS, pot.get(0).expression), M.Literal(1));
            }
            if(lo == null) {
                lo = treeutils.makeArrayLength(Position.NOPOS, M.Literal(0));
            }
            exprs = treeutils.makeOr(Position.NOPOS, exprs, treeutils.makeBinary(Position.NOPOS, Tag.GT, lhs.hi, hi));
            exprs = treeutils.makeOr(Position.NOPOS, exprs, treeutils.makeBinary(Position.NOPOS, Tag.LT, lhs.lo, lo));
        }
        expr = treeutils.makeAnd(Position.NOPOS, expr, exprs);
        for(int i = 1; i < pot.size(); ++i) {
            JCExpression expr1 = treeutils.makeNeqObject(Position.NOPOS, pot.get(i).expression, lhs.expression);
            if(pot.get(i).lo != null || pot.get(0).hi != null) {
                JCExpression hi = pot.get(i).hi;
                JCExpression lo = pot.get(i).lo;
                if(hi == null) {
                    hi = treeutils.makeBinary(Position.NOPOS, Tag.MINUS, treeutils.makeArrayLength(Position.NOPOS, pot.get(i).expression), M.Literal(1));
                }
                if(lo == null) {
                    lo = treeutils.makeArrayLength(Position.NOPOS, M.Literal(0));
                }
                expr1 = treeutils.makeOr(Position.NOPOS, expr1, treeutils.makeBinary(Position.NOPOS, Tag.GT, lhs.hi, hi));
                expr1 = treeutils.makeOr(Position.NOPOS, expr1, treeutils.makeBinary(Position.NOPOS, Tag.LT, lhs.lo, lo));
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
        List tmp = currentAssignable;
        currentAssignable = List.of(assignable);
        JCExpression res = editAssignable(lhs, false);
        currentAssignable = tmp;
        return res;

    }

    private JCExpression editAssignable(JCExpression lhs, JCExpression assignable, boolean ignoreLocals) {
        List tmp = currentAssignable;
        currentAssignable = List.of(assignable);
        JCExpression res = editAssignable(lhs, ignoreLocals);
        currentAssignable = tmp;
        return res;

    }

    @Override
    public JCTree visitJmlBlock(JmlBlock that, Void p) {
        List<JCStatement> orig = newStatements;
        List<JCStatement> l = List.nil();
        for(JCStatement st : that.getStatements()) {
            newStatements = List.nil();
            JCStatement copy = super.copy(st);
            if(newStatements.size() > 0) {
                l = l.appendList(newStatements);
            } else {
                l = l.append(copy);
            }
        }
        newStatements = orig.append(M.Block(0L, l));
        return that;
    }

    @Override
    public JCTree visitJmlStatementSpec(JmlStatementSpec that, Void p) {
        List<JCStatement> saveList = newStatements;
        newStatements = List.nil();
        super.copy(that.statementSpecs);
        super.copy(that.statements);

        newStatements = saveList.appendList(newStatements.prepend(M.Block(0L, combinedNewReqStatements)).
                append(M.Block(0L, combinedNewEnsStatements)));

        return that;
    }

    @Override
    public JCTree visitJmlMethodClauseExpr(JmlMethodClauseExpr that, Void p) {
        if(that.token == JmlTokenKind.ENSURES) {
            translationMode = VerifyFunctionVisitor.TranslationMode.ASSERT;
        } else if(that.token == JmlTokenKind.REQUIRES) {
            translationMode = VerifyFunctionVisitor.TranslationMode.ASSUME;
        }
        JCExpression copy = super.copy(that.expression);
        if(translationMode == VerifyFunctionVisitor.TranslationMode.ASSERT) {
            newStatements = newStatements.append(TranslationUtils.makeAssertStatement(copy, M));
            JCIf ifstmt = M.If(transUtils.makeNondetBoolean(currentMethod.sym), M.Block(0L, newStatements), null);
            newStatements = List.of(ifstmt);
            //newStatements = newStatements.append(TranslationUtils.makeAssertStatement(copy.expression, M));
            combinedNewEnsStatements = combinedNewEnsStatements.appendList(newStatements);
        } else if(translationMode == VerifyFunctionVisitor.TranslationMode.ASSUME){
            newStatements = newStatements.append(TranslationUtils.makeAssertStatement(copy, M));
            JCIf ifstmt = M.If(transUtils.makeNondetBoolean(currentMethod.sym), M.Block(0L, newStatements), null);
            newStatements = List.of(ifstmt);
            combinedNewReqStatements = combinedNewReqStatements.appendList(newStatements);
        }
        newStatements = List.nil();
        translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        return M.JmlMethodClauseExpr(that.token, copy);
    }

    @Override
    public JCTree visitMethodInvocation(MethodInvocationTree node, Void p) {
        if(translationMode != VerifyFunctionVisitor.TranslationMode.JAVA) {
        //    throw new RuntimeException("Method calls in specifications are currently not supported. (" + node.toString() + ")");
        }
        JCMethodInvocation copy = (JCMethodInvocation)super.visitMethodInvocation(node, p);
        if(copy.meth instanceof JCIdent) {
            //JCExpression expr = transUtils.checkConformAssignables(currentAssignable, baseVisitor.getAssignablesForName(copy.meth.toString()));
            //JCIf ifst = M.If(M.Unary(Tag.NOT, expr), makeException("Not conforming assignable clauses for method call: " + copy.meth.toString()), null);
            //newStatements = newStatements.append(ifst);
            copy.meth = M.Ident(copy.meth.toString() + "Symb");
        }
        List<JCExpression> assignables = baseVisitor.getAssignablesForName(((JCMethodInvocation)node).meth.toString());
        for(JCExpression e : assignables) {
            JCExpression cond = editAssignable(e);
            cond = treeutils.makeNot(Position.NOPOS, cond);
            JCStatement expr = TranslationUtils.makeAssertStatement(cond, M);
            newStatements = newStatements.append(expr);
        }
        return copy;
    }

    @Override
    public JCTree visitIf(IfTree node, Void p) {
        List <JCStatement> l = newStatements;
        newStatements = List.nil();
        JCStatement then = super.copy((JCStatement) node.getThenStatement());
        if(newStatements.size() > 1) {
            then = M.Block(0L, newStatements);
        } else if(newStatements.size() == 1) {
            then = newStatements.get(0);
        }
        newStatements = List.nil();
        JCStatement elseSt = super.copy((JCStatement) node.getElseStatement());
        if(newStatements.size() > 1) {
            elseSt = M.Block(0L, newStatements);
        } else if(newStatements.size() == 1) {
            then = newStatements.get(0);
        }
        JCExpression cond = super.copy((JCExpression)node.getCondition());
        newStatements = newStatements.appendList(l.append(M.If(cond, then, elseSt)));
        return (JCIf)node;
    }



    public List<JCStatement> getNewStatements() {
        return newStatements;
    }

    public Map<Integer, JCVariableDecl> getOldVars() {
        return oldVars;
    }

    public void setCurrentAssignable(List<JCExpression> currentAssignable) {
        this.currentAssignable = currentAssignable;
    }

    public VerifyFunctionVisitor.TranslationMode getTranslationMode() {
        return translationMode;
    }

    public void setTranslationMode(VerifyFunctionVisitor.TranslationMode translationMode) {
        this.translationMode = translationMode;
    }

    public JCIf getInnermostIf() {
        return innermostIf;
    }
}