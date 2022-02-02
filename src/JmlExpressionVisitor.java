import com.sun.source.tree.*;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Pair;
import com.sun.tools.javac.util.Position;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;

import static com.sun.tools.javac.tree.JCTree.*;
import static org.jmlspecs.openjml.JmlTree.*;

/**
 * Created by jklamroth on 11/14/18.
 */
public class JmlExpressionVisitor extends JmlTreeCopier {
    private static Logger log = LogManager.getLogger(JmlExpressionVisitor.class);
    private final Maker M;
    private final Names names;
    private final Symtab syms;
    private final JmlTreeUtils treeutils;
    private final ClassReader reader;
    private final Utils utils;
    private Symbol currentSymbol;
    private static int boolVarCounter = 0;
    private static int intVarCounter = 0;
    private static int paramVarCounter = 0;
    private List<JCStatement> newStatements = List.nil();
    private Symbol returnVar;
    private VerifyFunctionVisitor.TranslationMode translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
    //Has to perserve order (e.g. LinkedHashMap)
    private LinkedHashMap<String, JCVariableDecl> oldVars = new LinkedHashMap<>();
    private List<JCExpression> currentAssignable = List.nil();
    private Map<String, String> variableReplacements = new HashMap<>();
    //important that this is linkedHashMap as it perserves ordering
    private Map<Symbol.VarSymbol, Pair<JCExpression, JCExpression>> quantifierVars = new LinkedHashMap<>();
    private List<JCStatement> oldInits = List.nil();
    private List<Tag> supportedBinaryTags = List.of(Tag.PLUS, Tag.MINUS, Tag.MUL, Tag.DIV, Tag.MOD,
            Tag.BITXOR, Tag.BITOR, Tag.BITAND, Tag.SL, Tag.SR, Tag.AND, Tag.OR, Tag.EQ, Tag.NE,
            Tag.GE, Tag.GT, Tag.LE, Tag.LT, Tag.USR);
    private List<JCStatement> neededVariableDefs = List.nil();
    public boolean inConstructor = false;
    private static int numQuantvars = 0;
    private boolean forceOld = false;
    private boolean ignoreLocals = false;


    public JmlExpressionVisitor(Context context, Maker maker,
                                BaseVisitor base,
                                VerifyFunctionVisitor.TranslationMode translationMode,
                                LinkedHashMap<String, JCVariableDecl> oldVars,
                                Symbol returnVar,
                                JmlMethodDecl currentMethod) {
        super(context, maker);
        this.context = context;
        this.M = Maker.instance(context);
        this.names = Names.instance(context);
        this.syms = Symtab.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.utils = Utils.instance(context);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
        this.translationMode = translationMode;
        this.oldVars = oldVars;
        this.returnVar = returnVar;
        this.currentSymbol = currentMethod.sym;
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
    public JCTree visitConditionalExpression(ConditionalExpressionTree node, Void p) {
        JCConditional that = (JCConditional)node;
        VerifyFunctionVisitor.TranslationMode oldTranslationMode = translationMode;
        translationMode = VerifyFunctionVisitor.TranslationMode.DEMONIC;
        JCExpression cond = this.copy(that.cond);
        translationMode = oldTranslationMode;
        JCExpression ifpart = this.copy(that.truepart);
        JCExpression elsepart = this.copy(that.falsepart);
        return M.Conditional(cond, ifpart, elsepart);
    }

    @Override
    public JCTree visitJmlStatement(JmlStatement that, Void p) {
        if(that.keyword.equals("set")) {
            ErrorLogger.warn("Jml set statements only supported experimentally.");
            return that.statement;
        }
        throw new RuntimeException("Unsupported JmlStatement : " + that.toString());
    }

    @Override
    public JCTree visitJmlStatementExpr(JmlStatementExpr that, Void p) {
        JCExpression copy = null;
        if(that.clauseType.name().equals("assert")) {
            translationMode = VerifyFunctionVisitor.TranslationMode.ASSERT;
            JCExpression expr = TranslationUtils.unwrapExpression(that.expression);
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            copy = super.copy(expr, p);
            newStatements = newStatements.append(TranslationUtils.makeAssumeOrAssertStatement(copy, translationMode));
            newStatements = newStatements.prependList(neededVariableDefs);
            neededVariableDefs = List.nil();
            newStatements = tmp.append(M.Block(0L, newStatements));
            translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        } else if(that.clauseType.name().equals("assume")) {
            translationMode = VerifyFunctionVisitor.TranslationMode.ASSUME;
            JCExpression expr = TranslationUtils.unwrapExpression(that.expression);
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            copy = super.copy(expr, p);
            newStatements = newStatements.append(TranslationUtils.makeAssumeOrAssertStatement(copy, translationMode));
            newStatements = newStatements.prependList(neededVariableDefs);
            neededVariableDefs = List.nil();
            newStatements = tmp.append(M.Block(0L, newStatements));
            translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        } else {
            throw new RuntimeException("Token of kind " + that.clauseType.name() + " not supported.");
        }
        return M.JmlExpressionStatement(that.clauseType.name(), that.clauseType, that.label, copy);
    }

    @Override
    public JCTree visitUnary(UnaryTree node, Void p) {
        JCUnary u = (JCUnary)node;
        JCExpression argCopy = super.copy(u.arg);
        JCUnary copy = M.Unary(u.getTag(), argCopy);
        copy.operator = u.operator;
        copy = (JCUnary)copy.setType(u.type);
        if(u.getTag() == Tag.NOT || u.getTag() == Tag.NEG) {
            return copy;
        } else if(u.getTag() == Tag.POSTINC || u.getTag() == Tag.POSTDEC ||
                u.getTag() == Tag.PREDEC || u.getTag() == Tag.PREINC) {
            if(currentAssignable.stream().anyMatch(loc -> loc instanceof JmlStoreRefKeyword)) {
                return copy;
            }
            JCExpression cond = editAssignable(u.arg);
            if(cond != null) {
                JCStatement jcAssert = TranslationUtils.makeAssertStatement(treeutils.makeNot(Position.NOPOS, cond));
                newStatements = newStatements.append(jcAssert);
            }
            return copy;
        } else {
            throw new RuntimeException("Unsupported unary token: " + u.getTag() + " in " + node.toString());
        }
    }

    @Override
    public JCTree visitJmlChained(JmlChained that, Void p) {
        assert(that.conjuncts.size() >= 1);
        JCExpression expression = super.copy(that.conjuncts.head);
        for(int i = 1; i < that.conjuncts.size(); ++i) {
            expression = treeutils.makeAnd(Position.NOPOS, expression, super.copy(that.conjuncts.get(i)));
        }
        return expression;
    }

    @Override
    public JCTree visitJmlQuantifiedExpr(JmlQuantifiedExpr that, Void p) {
        if(that.decls.size() != 1) {
            throw new RuntimeException("Quantifiers only supported with exactly one declaration. (" + that.toString() + ")");
        }
        if(!that.decls.get(0).type.isNumeric()) {
            throw new RuntimeException("Only quantifiers with numeric variables support for now. (" + that.toString() + ")");
        }
        JmlQuantifiedExpr copy = (JmlQuantifiedExpr)that.clone();
        variableReplacements.put(that.decls.get(0).getName().toString(), "quantVar" + numQuantvars++ + that.decls.get(0).getName().toString());
        RangeExtractor re = new RangeExtractor(M, that.decls.get(0).sym);
        if(copy.range == null) {
            throw new RuntimeException("Only quantifiers with given ranges supported.");
        }
        JCExpression range = super.copy(copy.range);
        re.extractRange(range);
        JCExpression cond = super.copy(copy.range);
        quantifierVars.put(that.decls.get(0).sym, new Pair<>(re.getMin(), re.getMax()));

        if(copy.op == JmlTokenKind.BSFORALL) {
            if(translationMode == VerifyFunctionVisitor.TranslationMode.ASSERT) {
                JCVariableDecl quantVar = TranslationUtils.makeNondetIntVar(names.fromString(variableReplacements.get(that.decls.get(0).getName().toString())), currentSymbol);
                neededVariableDefs = neededVariableDefs.append(quantVar);
                if(cond == null) {
                    throw new RuntimeException("The program appears to contain unbounded quantifiers which are not supported by this tool (" + copy.toString() + ").");
                }
                for(Map.Entry<String, String> e : variableReplacements.entrySet()) {
                    cond = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), cond);
                }
                JCExpression res = treeutils.makeOr(Position.NOPOS, treeutils.makeNot(Position.NOPOS, cond), copy.value);
                List<JCStatement> old = newStatements;
                newStatements = List.nil();
                JCExpression value = super.copy(res);
                for(Map.Entry<String, String> e : variableReplacements.entrySet()) {
                    value = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), value);
                    newStatements = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), newStatements);
                }
                newStatements = newStatements.prependList(old);
//                JCUnary nexpr = treeutils.makeNot(Position.NOPOS, cond);
                variableReplacements.remove(that.decls.get(0).getName().toString());
                quantifierVars.remove(that.decls.get(0).sym);
                return value;
            } else if(translationMode == VerifyFunctionVisitor.TranslationMode.ASSUME || translationMode == VerifyFunctionVisitor.TranslationMode.DEMONIC) {
                List<JCStatement> stmts = newStatements;
                newStatements = List.nil();
                JCExpression value = super.copy(copy.value);
                JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentSymbol, treeutils.makeLit(Position.NOPOS, syms.booleanType, true));
                neededVariableDefs = neededVariableDefs.append(boolVar);
                JCBinary b = M.Binary(Tag.AND, M.Ident(boolVar), value);
                JCExpression init = super.copy(re.getMin());
                for(Map.Entry<String, String> e : variableReplacements.entrySet()) {
                    b = (JCBinary) TranslationUtils.replaceVarName(e.getKey(), e.getValue(), b);
                    range = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), range);
                    init = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), init);
                    newStatements = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), newStatements);
                }
                newStatements = newStatements.append(M.Exec(M.Assign(M.Ident(boolVar), b)));
                List<JCStatement> l = List.nil();
                //l = l.append(boolVar);
                String loopVarName = that.decls.get(0).getName().toString();
                if(variableReplacements.containsKey(that.decls.get(0).getName().toString())) {
                    loopVarName = variableReplacements.get(that.decls.get(0).getName().toString());
                }
                JCForLoop forLoop =  TranslationUtils.makeStandardLoopFromRange(range, newStatements, loopVarName, currentSymbol, init);
                l = l.append(forLoop);
                l = TranslationUtils.replaceVarName( that.decls.get(0).getName().toString(), variableReplacements.get(that.decls.get(0).getName().toString()), l);
                newStatements = stmts.appendList(l);
                variableReplacements.remove(that.decls.get(0).getName().toString());
                quantifierVars.remove(that.decls.get(0).sym);
                return M.Ident(boolVar);
            } else {
                throw new RuntimeException("Quantified expressions may not occure in Java-mode: " + that.toString());
            }
        } else if(copy.op == JmlTokenKind.BSEXISTS) {
            if(translationMode == VerifyFunctionVisitor.TranslationMode.ASSERT || translationMode == VerifyFunctionVisitor.TranslationMode.DEMONIC) {
                List<JCStatement> stmts = newStatements;
                newStatements = List.nil();
                JCExpression value = super.copy(copy.value);
                JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentSymbol, treeutils.makeLit(Position.NOPOS, syms.booleanType, false));
                neededVariableDefs = neededVariableDefs.append(boolVar);
                JCBinary b = M.Binary(Tag.OR, M.Ident(boolVar), value);
                JCExpression init = super.copy(re.getMin());
                for(Map.Entry<String, String> e : variableReplacements.entrySet()) {
                    b = (JCBinary) TranslationUtils.replaceVarName(e.getKey(), e.getValue(), b);
                    range = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), range);
                    init = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), init);
                    newStatements = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), newStatements);
                }
                newStatements = newStatements.append(M.Exec(M.Assign(M.Ident(boolVar), b)));
                List<JCStatement> l = List.nil();
                //l = l.append(boolVar);
                String loopVarName = that.decls.get(0).getName().toString();
                if(variableReplacements.containsKey(that.decls.get(0).getName().toString())) {
                    loopVarName = variableReplacements.get(that.decls.get(0).getName().toString());
                }
                l = l.append(TranslationUtils.makeStandardLoopFromRange(range, newStatements, loopVarName, currentSymbol, init));
                l = TranslationUtils.replaceVarName( that.decls.get(0).getName().toString(), variableReplacements.get(that.decls.get(0).getName().toString()), l);
                newStatements = stmts.appendList(l);
                variableReplacements.remove(that.decls.get(0).getName().toString());
                quantifierVars.remove(that.decls.get(0).sym);
                return M.Ident(boolVar);
            } else if(translationMode == VerifyFunctionVisitor.TranslationMode.ASSUME) {
                JCVariableDecl quantVar = TranslationUtils.makeNondetIntVar(names.fromString(variableReplacements.get(that.decls.get(0).getName().toString())), currentSymbol);
                neededVariableDefs = neededVariableDefs.append(quantVar);
                if(cond == null) {
                    throw new RuntimeException("The programm appears to contain unbounded quantifiers which are not supported by this tool (" + copy.toString() + ").");
                }
                for(Map.Entry<String, String> e : variableReplacements.entrySet()) {
                    cond = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), cond);
                }
                JCExpression res = treeutils.makeAnd(Position.NOPOS, cond, copy.value);
                List<JCStatement> old = newStatements;
                newStatements = List.nil();
                JCExpression value = super.copy(res);
                for(Map.Entry<String, String> e : variableReplacements.entrySet()) {
                    value = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), value);
                    newStatements = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), newStatements);
                }
                newStatements = newStatements.prependList(old);
//                JCUnary nexpr = treeutils.makeNot(Position.NOPOS, cond);
                variableReplacements.remove(that.decls.get(0).getName().toString());
                quantifierVars.remove(that.decls.get(0).sym);
                return value;
            } else {
                throw new RuntimeException("Quantified expressions may not occure in Java-mode: " + that.toString());
            }
        } else {
            throw new RuntimeException("Unkown token type in quantified Expression: " + copy.op);
        }
    }

//    @Override
//    public JCTree visitThrow(ThrowTree node, Void p) {
//        throw new RuntimeException("Throwing exceptions is currently not supported.");
//    }

    @Override
    public JCTree visitJmlBinary(JmlBinary that, Void p) {
        throw new RuntimeException("JmlBinaries should be normalized to JavaBinaries. (" + that.toString() + ")");
    }

    @Override
    public JCTree visitBinary(BinaryTree node, Void p) {
        if(!supportedBinaryTags.contains(((JCBinary)node).getTag())) {
            throw new RuntimeException("Unsupported Operation: " + node.toString() + "(" + ((JCBinary) node).getTag() + ")");
        }
        JCBinary b = (JCBinary)node;
        if(b.getTag() == Tag.OR) {
            JCExpression lhs = (JCExpression)this.copy((JCTree)b.lhs, p);
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            JCExpression rhs = (JCExpression)this.copy((JCTree)b.rhs, p);
            if(newStatements.size() != 0) {
                JCIf ifst = M.If(treeutils.makeNot(Position.NOPOS, lhs), M.Block(0L, newStatements), null);
                newStatements = tmp.append(ifst);
            } else {
                newStatements = tmp;
            }
            JCBinary res = M.Binary(b.getTag(), lhs, rhs);
            res = (JCBinary)res.setType(b.type);
            res.operator = b.operator;
            return res;
        } else if(b.getTag() == Tag.AND) {
            JCExpression lhs = (JCExpression)this.copy((JCTree)b.lhs, p);
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            JCExpression rhs = (JCExpression)this.copy((JCTree)b.rhs, p);
            if(newStatements.size() != 0) {
                JCIf ifst = M.If(lhs, M.Block(0L, newStatements), null);
                newStatements = tmp.append(ifst);
            } else {
                newStatements = tmp;
            }
            JCBinary res = M.Binary(b.getTag(), lhs, rhs);
            res = (JCBinary)res.setType(b.type);
            res.operator = b.operator;
            return res;
        }
        return super.visitBinary(node, p);
    }

    @Override
    public JCTree visitJmlMethodInvocation(JmlMethodInvocation that, Void p) {
        if (that.token == JmlTokenKind.BSOLD) {
            JCExpression argCopy = super.copy(that.getArguments().get(0));
            JCExpression arg = that.getArguments().get(0);
            if(!arg.toString().equals(argCopy.toString())) {
                throw new RuntimeException("Unsupported old expression: " + that.toString());
            }

            List<Symbol.VarSymbol> relevantQuantVars = List.nil();
            List<Symbol> identSymbols = IdentVisitor.getIdentSymbols(arg);
            for(Symbol.VarSymbol s : quantifierVars.keySet()) {
                if(identSymbols.contains(s)) {
                    relevantQuantVars = relevantQuantVars.append(s);
                }
            }
            JCVariableDecl oldVar;
            if (!oldVars.containsKey(arg.toString())) {
                if(quantifierVars.size() == 0 || relevantQuantVars.size() == 0) {
                    oldVar = treeutils.makeVarDef(arg.type, M.Name("old" + oldVars.size()), currentSymbol, argCopy);
                } else {
                    Type.ArrayType arrayType = new Type.ArrayType(argCopy.type, argCopy.type.tsym);
                    List<JCExpression> dims = List.nil();
                    for(int i = 0; i < relevantQuantVars.size(); ++i) {
                        JCExpression dim = M.Literal(CLI.maxArraySize);
                        dims = dims.append(dim);
                    }
                    for(int i = 0; i < relevantQuantVars.size() - 1; ++i) {
                        arrayType = new Type.ArrayType(arrayType, arrayType.tsym);
                    }
                    JCExpression init = M.NewArray(M.Type(arg.type), dims, null);
                    oldVar = treeutils.makeVarDef(arrayType, M.Name("old" + oldVars.size()), currentSymbol, init);


                    JCExpression bodyExp = M.Ident(oldVar);
                    for(Symbol.VarSymbol v : relevantQuantVars) {
                        bodyExp = treeutils.makeArrayElement(Position.NOPOS, bodyExp, treeutils.makeBinary(Position.NOPOS, Tag.MOD, treeutils.makeIdent(Position.NOPOS, v), M.Literal(CLI.maxArraySize)));
                    }
                    JCStatement body = treeutils.makeAssignStat(Position.NOPOS, bodyExp, argCopy);
                    JCStatement oldInit = null;
                    List<Symbol.VarSymbol> quanVars = List.from(quantifierVars.keySet());
                    quanVars = quanVars.reverse();
                    for(Symbol.VarSymbol v : quanVars) {
                        JCVariableDecl in = treeutils.makeVarDef(v.type, v.name, currentSymbol, quantifierVars.get(v).fst);

                        JCExpression c = super.copy(quantifierVars.get(v).snd);
                        oldInit = M.ForLoop(List.of(in), M.Binary(Tag.LE, M.Ident(in.sym), c), List.of(M.Exec(M.Unary(Tag.PREINC, M.Ident(in.sym)))), body);
                        body = oldInit;
                    }
                    oldInits = oldInits.append(oldInit);
                }
                oldVars.put(arg.toString(), oldVar);
            } else {
                oldVar = oldVars.get(arg.toString());
                if(oldVar == null) {
                    throw new RuntimeException("Couldnt find saved old expression: " + arg.toString());
                }
            }

            if(quantifierVars.size() == 0) {
                return M.Ident(oldVar);
            } else {
                JCExpression res = M.Ident(oldVar);
                for(Symbol.VarSymbol v : relevantQuantVars) {
                    res = treeutils.makeArrayElement(Position.NOPOS, res, treeutils.makeBinary(Position.NOPOS, Tag.MOD, treeutils.makeIdent(Position.NOPOS, v), M.Literal(CLI.maxArraySize)));
                }
                return res;
            }
        }
        throw new RuntimeException("JmlMethodInvocation with type " + that.token + " is not supported.");
    }

    @Override
    public JCTree visitJmlSingleton(JmlSingleton that, Void p) {
        if (that.token == JmlTokenKind.BSRESULT) {
            return M.Ident(returnVar);
        }
        throw new RuntimeException("JmlSingleton with type " + that.token + " is not supported.");
    }

    @Override
    public JCTree visitJmlStatementLoopExpr(JmlTree.JmlStatementLoopExpr that, Void p) {
        if(that.clauseType.name().equals("loop_invariant")) {
            return super.visitJmlStatementLoopExpr(that, p);
        } else if(that.clauseType.name().equals("decreases")) {
            return super.visitJmlStatementLoopExpr(that, p);
        }
        throw new RuntimeException("Token " + that.clauseType.name() + " for loop specifications currently not supported.");
    }

    @Override
    public JCTree visitSwitch(SwitchTree node, Void p) {
        throw new RuntimeException("Switch-Statements are currently not supported.");
    }

    @Override
    public JCTree visitCatch(CatchTree node, Void p) {
        List<JCStatement> tmp = newStatements;
        JCBlock body = (JCBlock)super.visitBlock(node.getBlock(), p);
        newStatements = tmp;
        return M.Catch((JCVariableDecl)node.getParameter(), body);
    }

    @Override
    public JCTree visitTry(TryTree node, Void p) {
        if(node.getFinallyBlock() != null) {
            throw new RuntimeException("Finally blocks currently not supported: " + node.toString());
        }
        JCExpression ty = M.Type(BaseVisitor.instance.getExceptionClass().type);
        JCCatch returnCatch = treeutils.makeCatcher(currentSymbol, ty.type);
        JCThrow throwStmt = M.Throw(M.NewClass(null, null, ty, List.nil(), null));
        returnCatch.body = M.Block(0L, List.of(throwStmt));
        List<JCCatch> catchers = List.nil();
        catchers = catchers.append(returnCatch);
        for(CatchTree c : node.getCatches()) {
            catchers = catchers.append((JCCatch)this.visitCatch(c, p));
        }
        List<JCStatement> tmp = newStatements;
        JCBlock body = (JCBlock)super.visitBlock(node.getBlock(), p);
        JCTry newTry = M.Try(body, catchers, null);
        newStatements = tmp;
        newStatements = newStatements.append(newTry);
        return newTry;
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
        if(that.loopSpecs == null || CLI.forceInliningLoops) {
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            if(that.body instanceof JCBlock) {
                super.copy(that.body);
                assert newStatements.size() == 1 && newStatements.get(0) instanceof JCBlock;
            } else {
                List<JCStatement> bodyStmts = List.of(that.body);
                JCBlock body = M.Block(0L, bodyStmts);
                super.copy(body);
            }
            assert(newStatements.size() == 1);
            JmlWhileLoop copy = M.WhileLoop(super.copy(that.cond), newStatements.get(0));
            newStatements = tmp.append(copy);
            return copy;
        }
        assumeOrAssertAllInvs(that.loopSpecs, VerifyFunctionVisitor.TranslationMode.ASSERT);
        List<JCExpression> assignables = List.nil();
        for(JmlTree.JmlStatementLoop spec : that.loopSpecs) {
            if (spec instanceof JmlStatementLoopModifies) {
                assignables = assignables.appendList(((JmlStatementLoopModifies) spec).storerefs);
            }
        }
        assignables = assignables.appendList(IdentifierVisitor.getAssignLocations(that.body));
        assignables = TranslationUtils.filterAssignables(assignables);
        assignables = assignables.reverse();
        newStatements = newStatements.appendList(TranslationUtils.havoc(assignables, currentSymbol, this));

        assumeOrAssertAllInvs(that.loopSpecs, VerifyFunctionVisitor.TranslationMode.ASSUME);
        JCVariableDecl oldD = null;
        JCExpression dExpr = null;
        for(JmlStatementLoop spec : that.loopSpecs) {
            if(spec instanceof JmlStatementLoopExpr && spec.clauseType.name().equals("loop_decreases")) {
                if(oldD != null) {
                    throw new RuntimeException("Only 1 decreases clause per loop allowed but found more.");
                }
                dExpr = super.copy(((JmlStatementLoopExpr) spec).expression);
                oldD = treeutils.makeIntVarDef(M.Name("oldDecreasesClauseValue" + intVarCounter++),  dExpr, currentSymbol);
                newStatements = newStatements.append(oldD);
            }
        }

        List<JCStatement> statements = newStatements;
        newStatements = List.nil();
        JCStatement assumefalse = TranslationUtils.makeAssumeStatement(treeutils.makeLit(Position.NOPOS, syms.booleanType, false));
        List<JCStatement> ifbodystatements = List.nil();
        translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        if(!(that.body instanceof JCBlock)) {
            that.body = M.Block(0L, List.of(that.body));
        }
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
                    TranslationUtils.makeAssertStatement(makeDereasesStatement(oldD, dExpr)));
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
            if(!(that.body instanceof JCBlock)) {
                that.body = M.Block(0L, List.of(that.body));
            }
            JmlDoWhileLoop copy = (JmlDoWhileLoop)super.visitJmlDoWhileLoop(that, p);
            assert(newStatements.size() == 1);
            copy.body = newStatements.get(0);
            newStatements = tmp.append(copy);
            return copy;
        }
        throw new RuntimeException("While-Loops with invariants currently not supported.");
    }

    @Override
    public JCTree visitJmlEnhancedForLoop(JmlEnhancedForLoop that, Void p) {
        if(that.loopSpecs != null) {
            throw new RuntimeException("Enhanced for loops with specifications are currently not supported.");
        }
        JmlEnhancedForLoop copy = (JmlEnhancedForLoop) that.clone();
        List<JCStatement> tmp = newStatements;
        newStatements = List.nil();
        JCStatement body = super.copy(that.body);
        assert(newStatements.size() == 1);
        copy.body = newStatements.head;
        newStatements = tmp;
        newStatements = newStatements.append(copy);
        return copy;
    }

    @Override
    public JCTree visitJmlForLoop(JmlTree.JmlForLoop that, Void p) {
        if(that.loopSpecs == null || CLI.forceInliningLoops) {
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            ArrayList<JCStatement> inits = new ArrayList<>();
            that.init.stream().forEach(el -> inits.add(super.copy(el)));
            List<JCStatement> tmp1 = newStatements;
            newStatements = List.nil();
            ArrayList<JCExpressionStatement> finalSteps = new ArrayList<>();
            //that.step.stream().forEach(el -> finalSteps.add(super.copy(el)));
            for(JCExpressionStatement st : that.step) {
                finalSteps.add(super.copy(st));
            }
            if(newStatements.size() == 0) {
                newStatements = List.from(finalSteps);
            }
            List<JCStatement> steps = newStatements;
            newStatements = List.nil();
            newStatements = tmp1;
            newStatements = TranslationUtils.diff(newStatements, List.from(inits));
            tmp = tmp.appendList(newStatements);
            newStatements = List.nil();
            if(that.body instanceof JCBlock) {
                super.copy(that.body);
                assert newStatements.size() == 1 && newStatements.get(0) instanceof JCBlock;
                newStatements = List.of(M.Block(0L, ((JCBlock) newStatements.get(0)).getStatements().appendList(steps)));
            } else {
                List<JCStatement> bodyStmts = List.of(that.body);
                bodyStmts = bodyStmts.appendList(steps);
                JCBlock body = M.Block(0L, bodyStmts);
                super.copy(body);
            }
            assert(newStatements.size() == 1);
            JmlForLoop copy = M.ForLoop(List.from(inits), super.copy(that.cond), List.nil(), newStatements.get(0));
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
        List<JCExpression> assignables = List.nil();
        assignables = assignables.append(M.Ident(loopVar));
        for(JmlTree.JmlStatementLoop spec : that.loopSpecs) {
            if (spec instanceof JmlStatementLoopModifies) {
                assignables = assignables.appendList(((JmlStatementLoopModifies) spec).storerefs);
            }
        }
        assignables = assignables.appendList(IdentifierVisitor.getAssignLocations(that.body));
        assignables = TranslationUtils.filterAssignables(assignables);
        assignables = assignables.reverse();
        newStatements = newStatements.appendList(TranslationUtils.havoc(assignables, currentSymbol, this));

        assumeOrAssertAllInvs(that.loopSpecs, VerifyFunctionVisitor.TranslationMode.ASSUME);
        JCVariableDecl oldD = null;
        JCExpression dExpr = null;
        for(JmlStatementLoop spec : that.loopSpecs) {
            if(spec instanceof JmlStatementLoopExpr && spec.clauseType.name().equals("loop_decreases")) {
                if(oldD != null) {
                    throw new RuntimeException("Only 1 decreases clause per loop allowed but found more.");
                }
                dExpr = super.copy(((JmlStatementLoopExpr) spec).expression);
                oldD = treeutils.makeIntVarDef(M.Name("oldDecreasesClauseValue" + intVarCounter++),  dExpr, currentSymbol);
                newStatements = newStatements.append(oldD);
            }
        }

        List<JCStatement> statements = newStatements;
        newStatements = List.nil();
        JCStatement assumefalse = TranslationUtils.makeAssumeStatement(treeutils.makeLit(Position.NOPOS, syms.booleanType, false));
        List<JCStatement> ifbodystatements = List.nil();
        translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        if(!(that.body instanceof JCBlock)) {
            that.body = M.Block(0L, List.of(that.body));
        }
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
                    TranslationUtils.makeAssertStatement(makeDereasesStatement(oldD, dExpr)));
        }
        JCBlock ifbody = M.Block(0L, ifbodystatements.append(assumefalse));
        newStatements = statements.append(M.If(that.cond, ifbody, null));
        return that;
    }

    private JCExpression makeDereasesStatement(JCVariableDecl oldD, JCExpression dExpr) {
        JCExpression res = M.Binary(Tag.GE, dExpr, M.Literal(0));
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
        JCExpression ty = M.Type(BaseVisitor.instance.getExceptionClass().type);
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
        List<JCStatement> oldNeededVars = neededVariableDefs;
        neededVariableDefs = List.nil();
        List<JCStatement> l = newStatements;
        newStatements = List.nil();
        VerifyFunctionVisitor.TranslationMode oldMode = translationMode;
        for(JmlTree.JmlStatementLoop spec : invs) {
            if(spec instanceof JmlStatementLoopExpr && spec.clauseType.name().equals("loop_invariant")) {
                translationMode = mode;
                JCExpression normalized = NormalizeVisitor.normalize(((JmlStatementLoopExpr) spec).expression, context, M);
                JCExpression assertCopy = this.copy(normalized);
                newStatements = newStatements.append(TranslationUtils.makeAssumeOrAssertStatement(assertCopy, mode));
            }
        }
        if(newStatements.size() > 0) {
            newStatements = l.append(M.Block(0L, newStatements.prependList(neededVariableDefs)));
            neededVariableDefs = List.nil();
        }
        translationMode = oldMode;
        neededVariableDefs = oldNeededVars;
    }


    @Override
    public JCTree visitAssignment(AssignmentTree node, Void p) {
        JCAssign assign = (JCAssign) node;
        if(currentAssignable.stream().anyMatch(loc -> loc instanceof JmlStoreRefKeyword)) {
            return super.visitAssignment(node, p);
        }
        JCExpression cond = editAssignable(assign.getVariable());
        if(cond != null) {
            cond = treeutils.makeNot(Position.NOPOS, cond);
            JCStatement expr = TranslationUtils.makeAssertStatement(cond);
            newStatements = newStatements.append(expr);
            //newStatements = newStatements.append(M.Exec(assign));
        }
        return super.visitAssignment(node, p);
    }

    @Override
    public JCTree visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
        JCAssignOp copy = (JCAssignOp)super.visitCompoundAssignment(node, p);
        if(copy.getTag() == Tag.PLUS_ASG ||
                copy.getTag() == Tag.MINUS_ASG ||
                copy.getTag() == Tag.BITAND_ASG ||
                copy.getTag() == Tag.BITOR_ASG ||
                copy.getTag() == Tag.BITXOR_ASG ||
                copy.getTag() == Tag.DIV_ASG ||
                copy.getTag() == Tag.MOD_ASG ||
                copy.getTag() == Tag.MUL_ASG ||
                copy.getTag() == Tag.SL_ASG ||
                copy.getTag() == Tag.SR_ASG ||
                copy.getTag() == Tag.USR_ASG) {
            if(currentAssignable.stream().anyMatch(loc -> loc instanceof JmlStoreRefKeyword)) {
                return copy;
            }
            JCExpression cond = editAssignable(copy.lhs);
            if(cond != null) {
                JCStatement assertSt = TranslationUtils.makeAssumeOrAssertStatement(treeutils.makeNot(Position.NOPOS, cond), VerifyFunctionVisitor.TranslationMode.ASSERT);
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
        return M.Throw(M.NewClass(null, null, ty, List.of(msgexpr), null));
    }

    public JCExpression editAssignable(JCExpression e, boolean ignoreLocals) {
        JCExpression copy = this.copy(e);
        this.ignoreLocals = ignoreLocals;
        JCExpression res = editAssignable(copy);
        this.ignoreLocals = false;
        return res;
    }

    public JCExpression editAssignable(JCExpression e) {
        if(e instanceof JCIdent) {
            if(!this.ignoreLocals && (((JCIdent) e).sym == null || ((JCIdent) e).sym.owner.equals(currentSymbol))) {
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
                    .anyMatch(as -> ((JCIdent)as).sym.equals(e.sym))) {
                return M.Literal(false);
            }
            if(currentAssignable.stream().filter(as -> as instanceof JCFieldAccess)
                    .anyMatch(as -> ((JCFieldAccess)as).sym.equals(e.sym))) {
                return M.Literal(false);
            }
            return M.Literal(true);
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
            JmlMethodInvocation oldExpr = M.JmlMethodInvocation(JmlTokenKind.BSOLD, pot.get(0));
            forceOld = true;
            JCExpression oldEx = this.copy(oldExpr);
            forceOld = false;
            JCExpression expr = treeutils.makeNeqObject(Position.NOPOS, oldEx, e);
            if(!pot.get(0).sym.owner.equals(currentSymbol) && !pot.get(0).toString().startsWith("this.") && !pot.get(0).toString().equals("this") && !oldVars.containsKey(pot.get(0).toString())) {
                expr = treeutils.makeNeqObject(Position.NOPOS, M.Ident("this." + pot.get(0)), e);
            }
            for(int i = 1; i < pot.size(); ++i) {
                JmlMethodInvocation oldExpr1 = M.JmlMethodInvocation(JmlTokenKind.BSOLD, pot.get(i));
                forceOld = true;
                JCExpression oldEx1 = this.copy(oldExpr1);
                forceOld = false;
                if(!pot.get(i).sym.owner.equals(currentSymbol) && !pot.get(i).toString().startsWith("this.") && !oldVars.containsKey(pot.get(i).toString())) {
                    JCExpression expr1 = treeutils.makeNeqObject(Position.NOPOS, M.Ident("this." + pot.get(i)), e);
                    expr = treeutils.makeAnd(Position.NOPOS, expr, expr1);
                } else {
                    JCExpression expr1 = treeutils.makeNeqObject(Position.NOPOS, oldEx1, e);
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
        JmlMethodInvocation oldExpr = M.JmlMethodInvocation(JmlTokenKind.BSOLD, pot.get(0).expression);
        forceOld = true;
        JCExpression oldEx = this.copy(oldExpr);
        forceOld = false;
        JCExpression exprs = treeutils.makeNeqObject(Position.NOPOS, oldEx, e.indexed);
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
            JmlMethodInvocation oldExpr1 = M.JmlMethodInvocation(JmlTokenKind.BSOLD, pot.get(i).expression);
            forceOld = true;
            JCExpression oldEx1 = this.copy(oldExpr1);
            forceOld = false;
            JCExpression expr1 = treeutils.makeNeqObject(Position.NOPOS, oldEx1, e.indexed);
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
        JmlMethodInvocation oldExpr = M.JmlMethodInvocation(JmlTokenKind.BSOLD, pot.get(0).expression);
        forceOld = true;
        JCExpression oldEx = this.copy(oldExpr);
        forceOld = false;
        JCExpression exprs = treeutils.makeNeqObject(Position.NOPOS, oldEx, e.expression);
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
                //.filter(i -> !i.type.isPrimitive())
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
            JmlMethodInvocation oldExpr = M.JmlMethodInvocation(JmlTokenKind.BSOLD, i);
            forceOld = true;
            JCExpression oldEx = this.copy(oldExpr);
            forceOld = false;
            if(expr == null) {
                expr = treeutils.makeNeqObject(Position.NOPOS, oldEx, f);
            } else {
                expr = treeutils.makeAnd(Position.NOPOS, expr, treeutils.makeNeqObject(Position.NOPOS, oldEx, f));
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
        throw new RuntimeException("JmlStatementSpecs not supported. (" + that.toString() + ")");
        //List<JCStatement> saveList = newStatements;
        //newStatements = List.nil();
        //super.copy(that.statementSpecs);
        //super.copy(that.statements.get(0));

        //newStatements = saveList.appendList(newStatements.prepend(M.Block(0L, combinedNewReqStatements)).
                //append(M.Block(0L, combinedNewEnsStatements)));

        ////dirty hack due to bug in OpenJML
        //saveList = newStatements;
        //for(JCStatement st : that.statements.tail) {
            //newStatements = List.nil();
            //JCStatement c = (JCStatement)super.copy(st);
            //if(newStatements.size() > 0) {
                //saveList = saveList.appendList(newStatements);
            //} else {
                //saveList = saveList.append(c);
            //}
        //}
        //newStatements = saveList;

        //return that;
    }

    @Override
    public JCTree visitJmlMethodClauseExpr(JmlMethodClauseExpr that, Void p) {
//        if(that.clauseKind == ensuresClauseKind) {
//            translationMode = VerifyFunctionVisitor.TranslationMode.ASSERT;
//        } else if(that.clauseKind == requiresClauseKind) {
//            translationMode = VerifyFunctionVisitor.TranslationMode.ASSUME;
//        }
//        JCExpression copy = super.copy(that.expression);
//        if(translationMode == VerifyFunctionVisitor.TranslationMode.ASSERT) {
//            newStatements = newStatements.append(TranslationUtils.makeAssertStatement(copy));
//            JCIf ifstmt = M.If(TranslationUtils.makeNondetBoolean(currentMethod.sym), M.Block(0L, newStatements), null);
//            newStatements = List.of(ifstmt);
//
//            //newStatements = newStatements.append(TranslationUtils.makeAssertStatement(copy.expression));
//            combinedNewEnsStatements = combinedNewEnsStatements.appendList(newStatements);
//        } else if(translationMode == VerifyFunctionVisitor.TranslationMode.ASSUME){
//            newStatements = newStatements.append(TranslationUtils.makeAssumeStatement(copy));
//            newStatements = List.of(M.Block(0L, newStatements));
//            combinedNewReqStatements = combinedNewReqStatements.appendList(newStatements);
//        }
//        newStatements = List.nil();
//        translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
//        return M.JmlMethodClauseExpr(that.clauseKind.name(), that.clauseKind, copy);
        ErrorLogger.warn("Blockcontracts are currently not supported (ignored).");
        return null;
    }

    @Override
    public JCTree visitNewClass(NewClassTree node, Void p) {
        JCNewClass newClass = (JCNewClass)node;
        if(newClass.def != null) {
            //anonymous class definition
            ErrorLogger.warn("Anonymous class definitions are only copied currently.");
            List<JCTree> newDefs = List.nil();
            for(JCTree d : newClass.def.defs) {
                if(!(d instanceof JmlMethodDecl)) {
                    newDefs = newDefs.append(d);
                } else {
                    if(!((JmlMethodDecl) d).name.toString().startsWith("<init>")) {
                        newDefs = newDefs.append(d);
                    }
                }
            }
            newClass.def.defs = newDefs;
            return newClass;
        }
        if(BaseVisitor.instance.hasSymbolicVersion(newClass.getIdentifier().toString())) {
            JCExpression ex = M.Ident(M.Name(newClass.getIdentifier() + "." + newClass.getIdentifier() + "Symb"));
            ex.setType(newClass.type);
            return M.App(ex, newClass.args);
        }
        return super.visitNewClass(node, p);
    }

    @Override
    public JCTree visitJmlVariableDecl(JmlVariableDecl that, Void p) {
        JmlVariableDecl copy = (JmlVariableDecl)super.visitJmlVariableDecl(that, p);
        newStatements = newStatements.append(copy);
        return copy;
    }

    @Override
    public JCTree visitMethodInvocation(MethodInvocationTree node, Void p) {
        if(translationMode != VerifyFunctionVisitor.TranslationMode.JAVA) {
            if(inConstructor) {
                JCMethodInvocation copy = (JCMethodInvocation)super.visitMethodInvocation(node, p);
                if(copy.meth instanceof JCIdent) {
                    copy.meth = treeutils.makeSelect(Position.NOPOS, M.Ident(returnVar), ((JCIdent) copy.meth).name);
                }
                return copy;
            }
            //throw new RuntimeException("Method calls in specifications are currently not supported. (" + node.toString() + ")");
            ErrorLogger.warn("Method calls in specifications only supported experimentally.");
          //  return (JCMethodInvocation)node;
        }
        JCMethodInvocation copy = (JCMethodInvocation)super.visitMethodInvocation(node, p);
        if(CLI.forceInliningMethods) {
            return copy;
        }
        String functionName = "";
        if(copy.meth instanceof JCIdent) {
            functionName = ((JCIdent) copy.meth).name.toString();
        } else if(copy.meth instanceof JCFieldAccess &&
                Objects.equals(copy.meth.type, currentSymbol.owner.type)) {
            functionName = ((JCFieldAccess) copy.meth).name.toString();
        }
        if(BaseVisitor.instance.hasSymbolicVersion(functionName) || copy.meth.toString().equals(currentSymbol.owner.name.toString())) {
            //JCExpression expr = TranslationUtils.checkConformAssignables(currentAssignable, baseVisitor.getAssignablesForName(copy.meth.toString()));
            //JCIf ifst = M.If(M.Unary(Tag.NOT, expr), makeException("Not conforming assignable clauses for method call: " + copy.meth.toString()), null);
            //newStatements = newStatements.append(ifst);

            if (currentAssignable.stream().noneMatch(loc -> loc instanceof JmlStoreRefKeyword)) {
                //log.warn("Framecondition for method invocations not yet supported.");
                Symbol oldSymbol = currentSymbol;
                if (copy.meth instanceof JCFieldAccess) {
                    currentSymbol = ((JCFieldAccess) copy.meth).sym;
                } else if(copy.meth instanceof JCIdent) {
                    currentSymbol = ((JCIdent) copy.meth).sym;
                } else {
                    throw new RuntimeException("method call that could not be handled " + copy.meth.toString());
                }
                List<JCExpression> assignables = BaseVisitor.instance.getAssignablesForName(functionName);
                assert(assignables != null);
                List<JCExpression> newargs = List.nil();
                for(JCExpression e : copy.args) {
                    JCVariableDecl saveParam = treeutils.makeVarDef(e.type, M.Name("$$param" + paramVarCounter++), oldSymbol, TranslationUtils.getLiteralForType(e.type));
                    neededVariableDefs = neededVariableDefs.append(saveParam);
                    JCStatement assign = M.Exec(M.Assign(M.Ident(saveParam), this.copy(e)));
                    newStatements = newStatements.append(assign);
                    newargs = newargs.append(treeutils.makeIdent(Position.NOPOS, saveParam.sym));
                }
                copy.args = newargs;
                for (JCExpression a : assignables) {
                    JCExpression cond = editAssignable(a, true);
                    cond = treeutils.makeNot(Position.NOPOS, cond);
                    Symbol.MethodSymbol sym = (Symbol.MethodSymbol) ((JCIdent)copy.meth).sym;
                    if (sym.params != null) {
                        for (int i = 0; i < sym.params.length(); ++i) {
                            cond = TranslationUtils.replaceVarName(sym.params.get(i).name.toString(), "$$param" + (paramVarCounter - sym.params.length() + i), cond);
                        }
                    }
                    newStatements = newStatements.append(TranslationUtils.makeAssumeOrAssertStatement(cond, VerifyFunctionVisitor.TranslationMode.ASSERT));
                }

                //for (JCExpression a : assignables) {

                //    JCExpression cond = editAssignable(a);
                //    cond = treeutils.makeNot(Position.NOPOS, cond);
                //    JCStatement ass = TranslationUtils.makeAssumeOrAssertStatement(cond, VerifyFunctionVisitor.TranslationMode.ASSERT);
                //    Symbol.MethodSymbol sym = (Symbol.MethodSymbol)currentSymbol;
                //    for(int i = 0; i < sym.params.length(); ++i) {
                //        ass = TranslationUtils.replaceVarName(sym.params.get(i).name.toString(), copy.args.get(i));
                //    }
                //    newStatements = newStatements.append(ass);
                //}
                currentSymbol = oldSymbol;
            }
            copy.meth = M.Ident(copy.meth.toString() + "Symb");

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
            elseSt = newStatements.get(0);
        }
        newStatements = List.nil();
        JCExpression cond = super.copy((JCExpression)node.getCondition());
        newStatements = newStatements.appendList(l.append(M.If(cond, then, elseSt)));
        return (JCIf)node;
    }

    @Override
    public JCTree visitIdentifier(IdentifierTree node, Void p) {
        if(inConstructor && ((JCIdent)node).sym.owner != currentSymbol && !node.getName().toString().equals("this")) {
            return M.Select(M.Ident(returnVar), (Name) node.getName());
        }
        return super.visitIdentifier(node, p);
    }

    @Override
    public JCTree visitMemberSelect(MemberSelectTree node, Void p) {
        return super.visitMemberSelect(node, p);
    }

    public List<JCStatement> getNewStatements() {
        return newStatements;
    }

    public void reset() {
        newStatements = List.nil();
        oldVars = new LinkedHashMap<>();
    }

    public LinkedHashMap<String, JCVariableDecl> getOldVars() {
        return oldVars;
    }

    public List<JCStatement> getOldInits() {
        return oldInits;
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

    public List<JCStatement> getNeededVariableDefs() {
        return neededVariableDefs;
    }
}
