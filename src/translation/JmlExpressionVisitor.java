package translation;

import static com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import static com.sun.tools.javac.tree.JCTree.JCAssign;
import static com.sun.tools.javac.tree.JCTree.JCAssignOp;
import static com.sun.tools.javac.tree.JCTree.JCBinary;
import static com.sun.tools.javac.tree.JCTree.JCBlock;
import static com.sun.tools.javac.tree.JCTree.JCCatch;
import static com.sun.tools.javac.tree.JCTree.JCConditional;
import static com.sun.tools.javac.tree.JCTree.JCExpression;
import static com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import static com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import static com.sun.tools.javac.tree.JCTree.JCForLoop;
import static com.sun.tools.javac.tree.JCTree.JCIdent;
import static com.sun.tools.javac.tree.JCTree.JCIf;
import static com.sun.tools.javac.tree.JCTree.JCLiteral;
import static com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import static com.sun.tools.javac.tree.JCTree.JCNewClass;
import static com.sun.tools.javac.tree.JCTree.JCStatement;
import static com.sun.tools.javac.tree.JCTree.JCThrow;
import static com.sun.tools.javac.tree.JCTree.JCTry;
import static com.sun.tools.javac.tree.JCTree.JCUnary;
import static com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import static com.sun.tools.javac.tree.JCTree.JCWhileLoop;
import static com.sun.tools.javac.tree.JCTree.Tag;
import static org.jmlspecs.openjml.JmlTree.JmlBinary;
import static org.jmlspecs.openjml.JmlTree.JmlBlock;
import static org.jmlspecs.openjml.JmlTree.JmlChained;
import static org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import static org.jmlspecs.openjml.JmlTree.JmlEnhancedForLoop;
import static org.jmlspecs.openjml.JmlTree.JmlForLoop;
import static org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import static org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import static org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import static org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import static org.jmlspecs.openjml.JmlTree.JmlSingleton;
import static org.jmlspecs.openjml.JmlTree.JmlStatement;
import static org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import static org.jmlspecs.openjml.JmlTree.JmlStatementLoop;
import static org.jmlspecs.openjml.JmlTree.JmlStatementLoopExpr;
import static org.jmlspecs.openjml.JmlTree.JmlStatementLoopModifies;
import static org.jmlspecs.openjml.JmlTree.JmlStatementSpec;
import static org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import static org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword;
import static org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import static org.jmlspecs.openjml.JmlTree.JmlWhileLoop;
import static org.jmlspecs.openjml.JmlTree.Maker;

import cli.CLI;
import cli.ErrorLogger;
import cli.TraceInformation;
import com.sun.source.tree.AssignmentTree;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.BreakTree;
import com.sun.source.tree.CaseTree;
import com.sun.source.tree.CatchTree;
import com.sun.source.tree.CompoundAssignmentTree;
import com.sun.source.tree.ConditionalExpressionTree;
import com.sun.source.tree.ContinueTree;
import com.sun.source.tree.ExpressionStatementTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.IfTree;
import com.sun.source.tree.LabeledStatementTree;
import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.ReturnTree;
import com.sun.source.tree.SwitchTree;
import com.sun.source.tree.TryTree;
import com.sun.source.tree.UnaryTree;
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
import exceptions.TranslationException;
import exceptions.UnsupportedException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import utils.IdentVisitor;
import utils.NormalizeVisitor;
import utils.RangeExtractor;
import utils.TranslationUtils;


/**
 * Created by jklamroth on 11/14/18.
 */
public class JmlExpressionVisitor extends JmlTreeCopier {
    private static final Logger log = LogManager.getLogger(JmlExpressionVisitor.class);
    private static int boolVarCounter = 0;
    private static int intVarCounter = 0;
    private static int paramVarCounter = 0;
    private static int numQuantvars = 0;
    private static int oldVarCounter = 0;
    private static List<Symbol.VarSymbol> loopLocalVars = List.nil();
    private final Maker maker;
    private final Names names;
    private final Symtab syms;
    private final JmlTreeUtils treeutils;
    private final ClassReader reader;
    private final Utils utils;
    private final Symbol returnVar;
    private final Map<String, String> variableReplacements = new HashMap<>();
    //important that this is linkedHashMap as it perserves ordering
    private final Map<Symbol.VarSymbol, Pair<JCExpression, JCExpression>> quantifierVars = new LinkedHashMap<>();
    private final List<Tag> supportedBinaryTags = List.of(Tag.PLUS, Tag.MINUS, Tag.MUL, Tag.DIV, Tag.MOD,
        Tag.BITXOR, Tag.BITOR, Tag.BITAND, Tag.SL, Tag.SR, Tag.AND, Tag.OR, Tag.EQ, Tag.NE,
        Tag.GE, Tag.GT, Tag.LE, Tag.LT, Tag.USR);
    public boolean inConstructor = false;
    private Symbol currentSymbol;
    private List<JCStatement> newStatements = List.nil();
    private VerifyFunctionVisitor.TranslationMode translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
    //Has to perserve order (e.g. LinkedHashMap)
    private LinkedHashMap<String, JCVariableDecl> oldVars = new LinkedHashMap<>();
    private List<JCExpression> currentAssignable = List.nil();
    private List<JCStatement> oldInits = List.nil();
    private List<JCStatement> neededVariableDefs = List.nil();
    private boolean forceOld = false;
    private boolean ignoreLocals = false;
    private List<JCVariableDecl> currentLoopVars = List.nil();
    private List<JCExpression> changedLocalVars = List.nil();


    public JmlExpressionVisitor(Context context, Maker maker,
                                BaseVisitor base,
                                VerifyFunctionVisitor.TranslationMode translationMode,
                                LinkedHashMap<String, JCVariableDecl> oldVars,
                                Symbol returnVar,
                                JmlMethodDecl currentMethod) {
        super(context, maker);
        this.context = context;
        this.maker = Maker.instance(context);
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
        JCExpression copy = super.copy((JCExpression) (node.getExpression()));
        if (newStatements.size() > 0) {
            newStatements = newStatements.append(maker.Exec(copy));
        }
        return maker.Exec(copy);
    }

    @Override
    public JCTree visitConditionalExpression(ConditionalExpressionTree node, Void p) {
        JCConditional that = (JCConditional) node;
        VerifyFunctionVisitor.TranslationMode oldTranslationMode = translationMode;
        translationMode = VerifyFunctionVisitor.TranslationMode.DEMONIC;
        JCExpression cond = this.copy(that.cond);
        translationMode = oldTranslationMode;
        JCExpression ifpart = this.copy(that.truepart);
        JCExpression elsepart = this.copy(that.falsepart);
        return maker.Conditional(cond, ifpart, elsepart);
    }

    @Override
    public JCTree visitJmlStatement(JmlStatement that, Void p) {
        if (that.keyword.equals("set")) {
            ErrorLogger.warn("Jml set statements only supported experimentally.");
            return that.statement;
        }
        throw new UnsupportedException("Unsupported JmlStatement : " + that);
    }

    @Override
    public JCTree visitJmlStatementExpr(JmlStatementExpr that, Void p) {
        JCExpression copy = null;
        if (that.clauseType.name().equals("assert")) {
            translationMode = VerifyFunctionVisitor.TranslationMode.ASSERT;
            JCExpression expr = TranslationUtils.unwrapExpression(that.expression);
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            List<JCStatement> oldNeededVariableDefs = neededVariableDefs;
            neededVariableDefs = List.nil();
            copy = super.copy(NormalizeVisitor.normalize(expr, context, M), p);
            newStatements = newStatements.append(TranslationUtils.makeAssumeOrAssertStatement(copy, translationMode));
            newStatements = newStatements.prependList(neededVariableDefs);
            neededVariableDefs = oldNeededVariableDefs;
            newStatements = tmp.append(maker.Block(0L, newStatements));
            translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        } else if (that.clauseType.name().equals("assume")) {
            translationMode = VerifyFunctionVisitor.TranslationMode.ASSUME;
            JCExpression expr = TranslationUtils.unwrapExpression(that.expression);
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            List<JCStatement> oldNeededVariableDefs = neededVariableDefs;
            neededVariableDefs = List.nil();
            copy = super.copy(NormalizeVisitor.normalize(expr, context, M), p);
            newStatements = newStatements.append(TranslationUtils.makeAssumeOrAssertStatement(copy, translationMode));
            newStatements = newStatements.prependList(neededVariableDefs);
            neededVariableDefs = oldNeededVariableDefs;
            newStatements = tmp.append(maker.Block(0L, newStatements));
            translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        } else {
            throw new UnsupportedException("Token of kind " + that.clauseType.name() + " not supported.");
        }
        return maker.JmlExpressionStatement(that.clauseType.name(), that.clauseType, that.label, copy);
    }

    @Override
    public JCTree visitUnary(UnaryTree node, Void p) {
        JCUnary u = (JCUnary) node;
        JCExpression argCopy = super.copy(u.arg);
        JCUnary copy = maker.Unary(u.getTag(), argCopy);
        copy.operator = u.operator;
        copy = (JCUnary) copy.setType(u.type);
        if (u.getTag() == Tag.NOT || u.getTag() == Tag.NEG) {
            return copy;
        } else if (u.getTag() == Tag.POSTINC || u.getTag() == Tag.POSTDEC ||
            u.getTag() == Tag.PREDEC || u.getTag() == Tag.PREINC) {
            newStatements = newStatements.appendList(makeAssignableAssertion(u.arg));
            return copy;
        } else {
            throw new UnsupportedException("Unsupported unary token: " + u.getTag() + " in " + node);
        }
    }

    @Override
    public JCTree visitJmlChained(JmlChained that, Void p) {
        assert (that.conjuncts.size() >= 1);
        JCExpression expression = super.copy(that.conjuncts.head);
        for (int i = 1; i < that.conjuncts.size(); ++i) {
            expression = treeutils.makeAnd(TranslationUtils.getCurrentPosition(), expression, super.copy(that.conjuncts.get(i)));
        }
        return expression;
    }

    @Override
    public JCTree visitJmlQuantifiedExpr(JmlQuantifiedExpr that, Void p) {
        if (that.decls.size() != 1) {
            throw new UnsupportedException("Quantifiers only supported with exactly one declaration. (" + that + ")");
        }
        if (!that.decls.get(0).type.isNumeric()) {
            throw new UnsupportedException("Only quantifiers with numeric variables supported for now. (" + that + ")");
        }
        JmlQuantifiedExpr copy = (JmlQuantifiedExpr) that.clone();
        variableReplacements.put(that.decls.get(0).getName().toString(), "quantVar" + numQuantvars++ + that.decls.get(0).getName().toString());
        CLI.expressionMap.put("quantVar" + (numQuantvars - 1) + that.decls.get(0).getName().toString(), that.decls.get(0).getName().toString());
        RangeExtractor re = new RangeExtractor(maker, that.decls.get(0).sym);
        if (copy.range == null) {
            throw new UnsupportedException("Only quantifiers with given ranges supported.");
        }
        JCExpression range = super.copy(copy.range);
        re.extractRange(range);
        JCExpression cond = super.copy(copy.range);
        quantifierVars.put(that.decls.get(0).sym, new Pair<>(re.getMin(), re.getMax()));

        if (copy.op == JmlTokenKind.BSFORALL) {
            if (translationMode == VerifyFunctionVisitor.TranslationMode.ASSERT) {
                JCVariableDecl quantVar = TranslationUtils.makeNondetIntVar(
                    names.fromString(variableReplacements.get(that.decls.get(0).getName().toString())),
                    currentSymbol
                );
                neededVariableDefs = neededVariableDefs.append(quantVar);
                if (cond == null) {
                    throw new UnsupportedException("The program appears to contain unbounded quantifiers which are not supported by this tool (" +
                        copy + ").");
                }
                for (Map.Entry<String, String> e : variableReplacements.entrySet()) {
                    cond = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), cond);
                }
                JCExpression res = treeutils.makeOr(
                    TranslationUtils.getCurrentPosition(),
                    treeutils.makeNot(TranslationUtils.getCurrentPosition(), cond),
                    copy.value
                );
                List<JCStatement> old = newStatements;
                newStatements = List.nil();
                JCExpression value = super.copy(res);
                for (Map.Entry<String, String> e : variableReplacements.entrySet()) {
                    value = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), value);
                    newStatements = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), newStatements);
                }
                newStatements = newStatements.prependList(old);
                variableReplacements.remove(that.decls.get(0).getName().toString());
                quantifierVars.remove(that.decls.get(0).sym);
                return value;
            } else if (translationMode == VerifyFunctionVisitor.TranslationMode.ASSUME ||
                translationMode == VerifyFunctionVisitor.TranslationMode.DEMONIC) {
                List<JCStatement> stmts = newStatements;
                newStatements = List.nil();
                JCExpression value = super.copy(copy.value);
                JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentSymbol,
                    treeutils.makeLit(TranslationUtils.getCurrentPosition(), syms.booleanType, true));
                neededVariableDefs = neededVariableDefs.append(boolVar);
                JCBinary b = maker.Binary(Tag.AND, maker.Ident(boolVar), value);
                JCExpression init = super.copy(re.getMin());
                for (Map.Entry<String, String> e : variableReplacements.entrySet()) {
                    b = (JCBinary) TranslationUtils.replaceVarName(e.getKey(), e.getValue(), b);
                    range = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), range);
                    init = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), init);
                    newStatements = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), newStatements);
                }
                newStatements = newStatements.append(maker.Exec(maker.Assign(maker.Ident(boolVar), b)));
                List<JCStatement> l = List.nil();
                //l = l.append(boolVar);
                String loopVarName = that.decls.get(0).getName().toString();
                if (variableReplacements.containsKey(that.decls.get(0).getName().toString())) {
                    loopVarName = variableReplacements.get(that.decls.get(0).getName().toString());
                }
                JCForLoop forLoop = TranslationUtils.makeStandardLoopFromRange(range, newStatements, loopVarName, currentSymbol, init);
                l = l.append(forLoop);
                l = TranslationUtils.replaceVarName(that.decls.get(0).getName().toString(),
                    variableReplacements.get(that.decls.get(0).getName().toString()), l);
                newStatements = stmts.appendList(l);
                variableReplacements.remove(that.decls.get(0).getName().toString());
                quantifierVars.remove(that.decls.get(0).sym);
                JCExpression translatedExpression = maker.Ident(boolVar);
                CLI.expressionMap.put(translatedExpression.toString(), that.toString());
                return translatedExpression;
            } else {
                throw new TranslationException("Quantified expressions may not occur in Java-mode: " + that);
            }
        } else if (copy.op == JmlTokenKind.BSEXISTS) {
            if (translationMode == VerifyFunctionVisitor.TranslationMode.ASSERT || translationMode == VerifyFunctionVisitor.TranslationMode.DEMONIC) {
                List<JCStatement> stmts = newStatements;
                newStatements = List.nil();
                JCExpression value = super.copy(copy.value);
                JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentSymbol,
                    treeutils.makeLit(TranslationUtils.getCurrentPosition(), syms.booleanType, false));
                neededVariableDefs = neededVariableDefs.append(boolVar);
                JCBinary b = maker.Binary(Tag.OR, maker.Ident(boolVar), value);
                JCExpression init = super.copy(re.getMin());
                for (Map.Entry<String, String> e : variableReplacements.entrySet()) {
                    b = (JCBinary) TranslationUtils.replaceVarName(e.getKey(), e.getValue(), b);
                    range = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), range);
                    init = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), init);
                    newStatements = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), newStatements);
                }
                newStatements = newStatements.append(maker.Exec(maker.Assign(maker.Ident(boolVar), b)));
                List<JCStatement> l = List.nil();
                //l = l.append(boolVar);
                String loopVarName = that.decls.get(0).getName().toString();
                if (variableReplacements.containsKey(that.decls.get(0).getName().toString())) {
                    loopVarName = variableReplacements.get(that.decls.get(0).getName().toString());
                }
                l = l.append(TranslationUtils.makeStandardLoopFromRange(range, newStatements, loopVarName, currentSymbol, init));
                l = TranslationUtils.replaceVarName(that.decls.get(0).getName().toString(),
                    variableReplacements.get(that.decls.get(0).getName().toString()), l);
                newStatements = stmts.appendList(l);
                variableReplacements.remove(that.decls.get(0).getName().toString());
                quantifierVars.remove(that.decls.get(0).sym);
                JCExpression translatedExpression = maker.Ident(boolVar);
                CLI.expressionMap.put(translatedExpression.toString(), that.toString());
                return translatedExpression;
            } else if (translationMode == VerifyFunctionVisitor.TranslationMode.ASSUME) {
                JCVariableDecl quantVar =
                    TranslationUtils.makeNondetIntVar(names.fromString(variableReplacements.get(that.decls.get(0).getName().toString())),
                        currentSymbol);
                neededVariableDefs = neededVariableDefs.append(quantVar);
                if (cond == null) {
                    throw new UnsupportedException(
                        "The program appears to contain unbounded quantifiers which are not supported by this tool (" + copy + ").");
                }
                for (Map.Entry<String, String> e : variableReplacements.entrySet()) {
                    cond = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), cond);
                }
                JCExpression res = treeutils.makeAnd(TranslationUtils.getCurrentPosition(), cond, copy.value);
                List<JCStatement> old = newStatements;
                newStatements = List.nil();
                JCExpression value = super.copy(res);
                for (Map.Entry<String, String> e : variableReplacements.entrySet()) {
                    value = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), value);
                    newStatements = TranslationUtils.replaceVarName(e.getKey(), e.getValue(), newStatements);
                }
                newStatements = newStatements.prependList(old);
                variableReplacements.remove(that.decls.get(0).getName().toString());
                quantifierVars.remove(that.decls.get(0).sym);
                return value;
            } else {
                throw new TranslationException("Quantified expressions may not occur in Java-mode: " + that);
            }
        } else {
            throw new UnsupportedException("Unkown token type in quantified Expression: " + copy.op);
        }
    }

    @Override
    public JCTree visitJmlBinary(JmlBinary that, Void p) {
        throw new TranslationException("JmlBinaries should be normalized to JavaBinaries. (" + that.toString() + ")");
    }

    @Override
    public JCTree visitBinary(BinaryTree node, Void p) {
        if (!supportedBinaryTags.contains(((JCBinary) node).getTag())) {
            throw new UnsupportedException("Unsupported Operation: " + node + "(" + ((JCBinary) node).getTag() + ")");
        }
        JCBinary b = (JCBinary) node;
        if (b.getTag() == Tag.OR) {
            JCExpression lhs = (JCExpression) this.copy((JCTree) b.lhs, p);
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            JCExpression rhs = (JCExpression) this.copy((JCTree) b.rhs, p);
            if (newStatements.size() != 0) {
                JCIf ifst = maker.If(treeutils.makeNot(TranslationUtils.getCurrentPosition(), lhs), maker.Block(0L, newStatements), null);
                newStatements = tmp.append(ifst);
            } else {
                newStatements = tmp;
            }
            JCBinary res = maker.Binary(b.getTag(), lhs, rhs);
            res = (JCBinary) res.setType(b.type);
            res.operator = b.operator;
            return res;
        } else if (b.getTag() == Tag.AND) {
            JCExpression lhs = (JCExpression) this.copy((JCTree) b.lhs, p);
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            JCExpression rhs = (JCExpression) this.copy((JCTree) b.rhs, p);
            if (newStatements.size() != 0) {
                JCIf ifst = maker.If(lhs, maker.Block(0L, newStatements), null);
                newStatements = tmp.append(ifst);
            } else {
                newStatements = tmp;
            }
            JCBinary res = maker.Binary(b.getTag(), lhs, rhs);
            res = (JCBinary) res.setType(b.type);
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
            if (!arg.toString().equals(argCopy.toString())) {
                throw new UnsupportedException("Unsupported old expression: " + that);
            }

            List<Symbol.VarSymbol> relevantQuantVars = List.nil();
            List<Symbol> identSymbols = IdentVisitor.getIdentSymbols(arg);
            for (Symbol.VarSymbol s : quantifierVars.keySet()) {
                if (identSymbols.contains(s)) {
                    relevantQuantVars = relevantQuantVars.append(s);
                }
            }
            JCVariableDecl oldVar;
            if (!oldVars.containsKey(arg.toString())) {
                if (quantifierVars.size() == 0 || relevantQuantVars.size() == 0) {
                    oldVar = treeutils.makeVarDef(arg.type, maker.Name("old" + oldVarCounter++), currentSymbol, argCopy);
                } else {
                    Type.ArrayType arrayType = new Type.ArrayType(argCopy.type, argCopy.type.tsym);
                    List<JCExpression> dims = List.nil();
                    for (int i = 0; i < relevantQuantVars.size(); ++i) {
                        JCExpression dim = maker.Literal(CLI.maxArraySize);
                        dims = dims.append(dim);
                    }
                    for (int i = 0; i < relevantQuantVars.size() - 1; ++i) {
                        arrayType = new Type.ArrayType(arrayType, arrayType.tsym);
                    }
                    JCExpression init = maker.NewArray(maker.Type(arg.type), dims, null);
                    oldVar = treeutils.makeVarDef(arrayType, maker.Name("old" + oldVarCounter++), currentSymbol, init);


                    JCExpression bodyExp = maker.Ident(oldVar);
                    for (Symbol.VarSymbol v : relevantQuantVars) {
                        bodyExp = treeutils.makeArrayElement(TranslationUtils.getCurrentPosition(), bodyExp,
                            treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.MOD,
                                treeutils.makeIdent(TranslationUtils.getCurrentPosition(), v), maker.Literal(CLI.maxArraySize)));
                    }
                    JCStatement body = treeutils.makeAssignStat(TranslationUtils.getCurrentPosition(), bodyExp, argCopy);
                    JCStatement oldInit = null;
                    List<Symbol.VarSymbol> quanVars = List.from(quantifierVars.keySet());
                    quanVars = quanVars.reverse();
                    for (Symbol.VarSymbol v : quanVars) {
                        JCVariableDecl in = treeutils.makeVarDef(v.type, v.name, currentSymbol, quantifierVars.get(v).fst);

                        JCExpression c = super.copy(quantifierVars.get(v).snd);
                        oldInit = maker.ForLoop(List.of(in), maker.Binary(Tag.LE, maker.Ident(in.sym), c),
                            List.of(maker.Exec(maker.Unary(Tag.PREINC, maker.Ident(in.sym)))), body);
                        body = oldInit;
                    }
                    oldInits = oldInits.append(oldInit);
                }
                oldVars.put(arg.toString(), oldVar);
                TraceInformation.ignoredVars.add(oldVar.name.toString());
                //CLI.expressionMap.put(maker.Ident(oldVar).toString(), that.toString());
            } else {
                oldVar = oldVars.get(arg.toString());
                if (oldVar == null) {
                    throw new TranslationException("Couldnt find saved old expression: " + arg);
                }
            }

            if (quantifierVars.size() == 0) {
                return maker.Ident(oldVar);
            } else {
                JCExpression res = maker.Ident(oldVar);
                for (Symbol.VarSymbol v : relevantQuantVars) {
                    res = treeutils.makeArrayElement(TranslationUtils.getCurrentPosition(), res,
                        treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.MOD,
                            treeutils.makeIdent(TranslationUtils.getCurrentPosition(), v), maker.Literal(CLI.maxArraySize)));
                }
                return res;
            }
        }
        throw new TranslationException("JmlMethodInvocation with type " + that.token + " is not supported.");
    }

    @Override
    public JCTree visitJmlSingleton(JmlSingleton that, Void p) {
        if (that.token == JmlTokenKind.BSRESULT) {
            return maker.Ident(returnVar);
        }
        throw new TranslationException("JmlSingleton with type " + that.token + " is not supported.");
    }

    @Override
    public JCTree visitJmlStatementLoopExpr(JmlTree.JmlStatementLoopExpr that, Void p) {
        if (that.clauseType.name().equals("loop_invariant")) {
            return super.visitJmlStatementLoopExpr(that, p);
        } else if (that.clauseType.name().equals("decreases")) {
            return super.visitJmlStatementLoopExpr(that, p);
        }
        throw new TranslationException("Token " + that.clauseType.name() + " for loop specifications currently not supported.");
    }

    @Override
    public JCTree visitSwitch(SwitchTree node, Void p) {
        throw new TranslationException("Switch-Statements are currently not supported.");
    }

    @Override
    public JCTree visitCatch(CatchTree node, Void p) {
        List<JCStatement> tmp = newStatements;
        JCBlock body = (JCBlock) super.visitBlock(node.getBlock(), p);
        newStatements = tmp;
        return maker.Catch((JCVariableDecl) node.getParameter(), body);
    }

    @Override
    public JCTree visitTry(TryTree node, Void p) {
        if (node.getFinallyBlock() != null) {
            throw new TranslationException("Finally blocks currently not supported: " + node);
        }
        JCExpression ty = maker.Type(BaseVisitor.instance.getExceptionClass().type);
        JCCatch returnCatch = treeutils.makeCatcher(currentSymbol, ty.type);
        JCThrow throwStmt = maker.Throw(maker.NewClass(null, null, ty, List.nil(), null));
        returnCatch.body = maker.Block(0L, List.of(throwStmt));
        List<JCCatch> catchers = List.nil();
        catchers = catchers.append(returnCatch);
        for (CatchTree c : node.getCatches()) {
            catchers = catchers.append((JCCatch) this.visitCatch(c, p));
        }
        List<JCStatement> tmp = newStatements;
        JCBlock body = (JCBlock) super.visitBlock(node.getBlock(), p);
        JCTry newTry = maker.Try(body, catchers, null);
        newStatements = tmp;
        newStatements = newStatements.append(newTry);
        return newTry;
    }

    @Override
    public JCTree visitCase(CaseTree node, Void p) {
        throw new TranslationException("Case-Statements are currently not supported.");
    }

    @Override
    public JCTree visitBreak(BreakTree node, Void p) {
        throw new UnsupportedException("Break-Statements are currently not supported.");
    }

    @Override
    public JCTree visitContinue(ContinueTree node, Void p) {
        if (CLI.forceInliningLoops) {
            return super.visitContinue(node, p);
        }
        throw new UnsupportedException("Continue-Statements are currently only supported when inlining.");
    }

    @Override
    public JCTree visitJmlWhileLoop(JmlWhileLoop that, Void p) {
        if (that.loopSpecs == null || CLI.forceInliningLoops) {
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            if (that.body instanceof JCBlock) {
                super.copy(that.body);
                assert newStatements.size() == 1 && newStatements.get(0) instanceof JCBlock;
            } else {
                List<JCStatement> bodyStmts = List.of(that.body);
                JCBlock body = maker.Block(0L, bodyStmts);
                super.copy(body);
            }
            assert (newStatements.size() == 1);
            JmlWhileLoop copy = maker.WhileLoop(super.copy(that.cond), newStatements.get(0));
            newStatements = tmp.append(copy);
            return copy;
        }
        List<JCExpression> oldAssignbales = currentAssignable;
        List<JCStatement> oldInitsOld = oldInits;
        oldInits = List.nil();
        LinkedHashMap<String, JCVariableDecl> oldVarsOld = oldVars;
        oldVars = new LinkedHashMap<>();
        List<JCExpression> oldChangedLocalVars = changedLocalVars;
        changedLocalVars = List.nil();
        List<Symbol.VarSymbol> oldLoopLocalVars = loopLocalVars;
        loopLocalVars = List.nil();

        List<JCStatement> assertInitInvs = assumeOrAssertAllInvs(that.loopSpecs, VerifyFunctionVisitor.TranslationMode.ASSERT);
        List<JCExpression> assignables = List.nil();
        for (JmlTree.JmlStatementLoop spec : that.loopSpecs) {
            if (spec instanceof JmlStatementLoopModifies) {
                assignables = assignables.appendList(((JmlStatementLoopModifies) spec).storerefs);
            }
        }
        if (assignables.size() == 0) {
            assignables = assignables.append(maker.JmlStoreRefKeyword(JmlTokenKind.BSEVERYTHING));
        }
        if (assignables.size() == 1 && assignables.get(0) instanceof JmlStoreRefKeyword &&
            ((JmlStoreRefKeyword) assignables.get(0)).token == JmlTokenKind.BSNOTHING) {
            assignables = List.nil();
        }
        for (JCExpression e : assignables) {
            assertInitInvs = assertInitInvs.appendList(makeAssignableAssertion(e));
        }
        for (JCVariableDecl decl : currentLoopVars) {
            assignables = assignables.append(maker.Ident(decl));
        }
        //assignables = assignables.appendList(Utils.IdentifierVisitor.getAssignLocations(that.body));
        assignables = TranslationUtils.filterAssignables(assignables);
        //List<JCStatement> havocStatements = Utils.TranslationUtils.havoc(assignables, currentSymbol, this);
        currentAssignable = assignables;

        List<JCStatement> assumeInvs = assumeOrAssertAllInvs(that.loopSpecs, VerifyFunctionVisitor.TranslationMode.ASSUME);
        JCVariableDecl oldD = null;
        JCExpression expression = null;
        List<JCStatement> oldDecreases = List.nil();
        for (JmlStatementLoop spec : that.loopSpecs) {
            if (spec instanceof JmlStatementLoopExpr && spec.clauseType.name().equals("loop_decreases")) {
                if (oldD != null) {
                    throw new TranslationException("Only 1 decreases clause per loop allowed but found more.");
                }
                expression = super.copy(((JmlStatementLoopExpr) spec).expression);
                oldD = treeutils.makeIntVarDef(maker.Name("oldDecreasesClauseValue" + intVarCounter++), expression, currentSymbol);
                oldDecreases = oldDecreases.append(oldD);
            }
        }

        List<JCStatement> statements = newStatements;
        newStatements = List.nil();
        JCStatement assumefalse =
            TranslationUtils.makeAssumeStatement(treeutils.makeLit(TranslationUtils.getCurrentPosition(), syms.booleanType, false));
        List<JCStatement> ifbodystatements = List.nil();
        translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        if (!(that.body instanceof JCBlock)) {
            that.body = maker.Block(0L, List.of(that.body));
        }
        changedLocalVars = List.nil();
        for (JCStatement st : ((JCBlock) that.body).getStatements()) {
            JCStatement stcopy = super.copy(st);
            if (newStatements.size() == 0) {
                ifbodystatements = ifbodystatements.append(stcopy);
            } else {
                ifbodystatements = ifbodystatements.appendList(newStatements);
                newStatements = List.nil();
            }
        }
        assignables = assignables.reverse();
        assignables = assignables.appendList(changedLocalVars);
        List<JCStatement> havocStatements = TranslationUtils.havoc(assignables, currentSymbol, this);
        List<JCStatement> assertInvs = assumeOrAssertAllInvs(that.loopSpecs, VerifyFunctionVisitor.TranslationMode.ASSERT);
        currentAssignable = oldAssignbales;
        ifbodystatements = ifbodystatements.appendList(assertInvs);
        if (expression != null) {
            ifbodystatements = ifbodystatements.append(
                TranslationUtils.makeAssertStatement(makeDereasesStatement(oldD, expression)));
        }

        List<JCStatement> prepareOldVarsSt = List.nil();
        for (JCVariableDecl variableDecl : oldVars.values()) {
            prepareOldVarsSt = prepareOldVarsSt.append(variableDecl);
        }

        for (JCStatement oldInit : oldInits) {
            prepareOldVarsSt = prepareOldVarsSt.append(oldInit);
        }
        JCBlock ifbody = maker.Block(0L, ifbodystatements.append(assumefalse));
        newStatements = statements.appendList(prepareOldVarsSt)
            .appendList(assertInitInvs)
            .appendList(oldDecreases)
            .appendList(havocStatements)
            .appendList(assumeInvs)
            .append(maker.If(that.cond, ifbody, null));

        oldInits = oldInitsOld;
        oldVars = oldVarsOld;
        changedLocalVars = oldChangedLocalVars;
        loopLocalVars = oldLoopLocalVars;
        return that;
    }

    @Override
    public JCTree visitJmlDoWhileLoop(JmlDoWhileLoop that, Void p) {
        if (that.loopSpecs == null) {
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            if (!(that.body instanceof JCBlock)) {
                that.body = maker.Block(0L, List.of(that.body));
            }
            JmlDoWhileLoop copy = (JmlDoWhileLoop) super.visitJmlDoWhileLoop(that, p);
            assert (newStatements.size() == 1);
            copy.body = newStatements.get(0);
            newStatements = tmp.append(copy);
            return copy;
        }
        throw new TranslationException("While-Loops with invariants currently not supported.");
    }


    @Override
    public JCTree visitLabeledStatement(LabeledStatementTree node, Void p) {
        List<JCStatement> tmp = newStatements;
        newStatements = List.nil();
        JCTree.JCLabeledStatement lst = (JCTree.JCLabeledStatement) super.visitLabeledStatement(node, p);
        if (newStatements.isEmpty()) {
            return lst;
        } else {
            if (newStatements.size() == 1) {
                lst.body = newStatements.get(0);
                newStatements = List.of(lst);
            } else {
                lst.body = M.Block(0L, newStatements);
                newStatements = List.of(lst);
            }
        }
        newStatements = newStatements.prependList(tmp);
        return lst;
    }

    @Override
    public JCTree visitJmlEnhancedForLoop(JmlEnhancedForLoop that, Void p) {
        if (that.loopSpecs != null) {
            throw new TranslationException("Enhanced for loops with specifications are currently not supported.");
        }
        JmlEnhancedForLoop copy = (JmlEnhancedForLoop) that.clone();
        List<JCStatement> tmp = newStatements;
        newStatements = List.nil();
        JCStatement body = super.copy(that.body);
        assert (newStatements.size() == 1);
        copy.body = newStatements.head;
        newStatements = tmp;
        newStatements = newStatements.append(copy);
        return copy;
    }

    @Override
    public JCTree visitJmlForLoop(JmlTree.JmlForLoop that, Void p) {
        if (that.loopSpecs == null || CLI.forceInliningLoops) {
            List<JCStatement> tmp = newStatements;
            newStatements = List.nil();
            ArrayList<JCStatement> inits = new ArrayList<>();
            that.init.stream().forEach(el -> inits.add(super.copy(el)));
            List<JCStatement> tmp1 = newStatements;
            newStatements = List.nil();
            ArrayList<JCExpressionStatement> finalSteps = new ArrayList<>();
            //that.step.stream().forEach(el -> finalSteps.add(super.copy(el)));
            for (JCExpressionStatement st : that.step) {
                finalSteps.add(super.copy(st));
            }
            if (newStatements.size() == 0) {
                newStatements = List.from(finalSteps);
            }
            List<JCStatement> steps = newStatements;
            newStatements = tmp1;
            newStatements = TranslationUtils.diff(newStatements, List.from(inits));
            tmp = tmp.appendList(newStatements);
            newStatements = List.nil();
            if (that.body instanceof JCBlock) {
                super.copy(that.body);
                assert newStatements.size() == 1 && newStatements.get(0) instanceof JCBlock;
                newStatements = List.of(maker.Block(0L, ((JCBlock) newStatements.get(0)).getStatements().appendList(steps)));
            } else {
                List<JCStatement> bodyStmts = List.of(that.body);
                bodyStmts = bodyStmts.appendList(steps);
                JCBlock body = maker.Block(0L, bodyStmts);
                super.copy(body);
            }
            assert (newStatements.size() == 1);
            JmlForLoop copy = maker.ForLoop(List.from(inits), super.copy(that.cond), List.nil(), newStatements.get(0));
            newStatements = tmp.append(copy);
            return copy;
        }

        currentLoopVars = List.nil();
        for (JCStatement st : that.init) {
            if (st instanceof JCVariableDecl) {
                this.currentLoopVars = currentLoopVars.append((JCVariableDecl) st);
            } else {
                throw new UnsupportedException("Unsupported init in for loop: " + st + " (only variable declarations allowed)");
            }
        }

        if (!(that.body instanceof JCBlock)) {
            that.body = maker.Block(0L, List.of(that.body));
        }
        for (JCExpressionStatement st : that.step) {
            ((JCBlock) that.body).stats = ((JCBlock) that.body).stats.append(st);
        }
        JCWhileLoop whileConvertion = maker.JmlWhileLoop(maker.WhileLoop(that.cond, that.body), that.loopSpecs);
        JCBlock block = maker.Block(0L, List.of(whileConvertion));
        for (JCStatement decl : that.init) {
            block.stats = block.stats.prepend(decl);
        }
        super.copy(block);
        return that;
    }

    private JCExpression makeDereasesStatement(JCVariableDecl oldD, JCExpression expression) {
        JCExpression res = maker.Binary(Tag.GE, expression, maker.Literal(0));
        JCExpression snd = maker.Binary(Tag.LT, expression, maker.Ident(oldD.name));
        return maker.Binary(Tag.AND, res, snd);
    }

    @Override
    public JCTree visitReturn(ReturnTree node, Void p) {
        JCExpression expressionCopy = super.copy((JCExpression) node.getExpression(), p);
        JCAssign assign = null;
        if (returnVar != null) {
            assign = maker.Assign(maker.Ident(returnVar), expressionCopy);
        }
        JCExpression ty = maker.Type(BaseVisitor.instance.getExceptionClass().type);
        JCThrow throwStmt = maker.Throw(maker.NewClass(null, null, ty, List.nil(), null));
        if (assign != null) {
            JCBlock block = maker.Block(0L, List.of(maker.Exec(assign), throwStmt));
            if (newStatements.size() == 0) {
                return block;
            } else {
                newStatements = newStatements.append(block);
                return block;
            }
        } else {
            JCBlock block = maker.Block(0L, List.of(throwStmt));
            if (newStatements.size() == 0) {
                return block;
            } else {
                newStatements = newStatements.append(block);
                return block;
            }
        }
    }

    private List<JCStatement> assumeOrAssertAllInvs(List<JmlStatementLoop> invs, VerifyFunctionVisitor.TranslationMode mode) {
        JCTree oldEnsures = TranslationUtils.getCurrentEnsures();
        List<JCStatement> oldNeededVars = neededVariableDefs;
        neededVariableDefs = List.nil();
        List<JCStatement> l = newStatements;
        newStatements = List.nil();
        VerifyFunctionVisitor.TranslationMode oldMode = translationMode;
        for (JmlTree.JmlStatementLoop spec : invs) {
            if (spec instanceof JmlStatementLoopExpr && spec.clauseType.name().equals("loop_invariant")) {
                translationMode = mode;
                JCExpression normalized = NormalizeVisitor.normalize(((JmlStatementLoopExpr) spec).expression, context, maker);
                JCExpression assertCopy = this.copy(normalized);
                TranslationUtils.setCurrentEnsures(spec);
                newStatements = newStatements.append(TranslationUtils.makeAssumeOrAssertStatement(assertCopy, mode));
            }
        }
        List<JCStatement> res = List.nil();
        if (newStatements.size() > 0) {
            res = List.of(maker.Block(0L, newStatements.prependList(neededVariableDefs)));
        }
        newStatements = l;
        translationMode = oldMode;
        neededVariableDefs = oldNeededVars;
        TranslationUtils.setCurrentEnsures(oldEnsures);
        return res;
    }


    @Override
    public JCTree visitAssignment(AssignmentTree node, Void p) {
        JCAssign assign = (JCAssign) node;
        JCExpression cond = editAssignable(assign.getVariable());
        if (cond != null) {
            cond = treeutils.makeNot(TranslationUtils.getCurrentPosition(), cond);
            JCStatement expr = TranslationUtils.makeAssertStatement(cond);
            newStatements = newStatements.append(expr);
            //newStatements = newStatements.append(M.Exec(assign));
        }
        return super.visitAssignment(node, p);
    }

    @Override
    public JCTree visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
        JCAssignOp copy = (JCAssignOp) super.visitCompoundAssignment(node, p);
        if (copy.getTag() == Tag.PLUS_ASG ||
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
            newStatements = newStatements.appendList(makeAssignableAssertion(copy.lhs));
            return copy;
        } else {
            throw new UnsupportedException("Unkonwn assignment type " + copy);
        }
    }


    public JCThrow makeException(String msg) {
        JCExpression ty = maker.Type(syms.runtimeExceptionType);
        JCTree.JCExpression msgexpr = treeutils.makeStringLiteral(TranslationUtils.getCurrentPosition(), msg);
        return maker.Throw(maker.NewClass(null, null, ty, List.of(msgexpr), null));
    }

    public JCExpression editAssignable(JCExpression e, boolean ignoreLocals) {
        JCExpression copy = this.copy(e);
        this.ignoreLocals = ignoreLocals;
        JCExpression res = editAssignable(copy);
        this.ignoreLocals = false;
        return res;
    }

    public List<JCStatement> makeAssignableAssertion(JCExpression expr) {
        JCExpression cond = editAssignable(expr);
        if (cond instanceof JCLiteral && ((JCLiteral) cond).getValue().equals(false)) {
            return List.nil();
        }
        return List.of(TranslationUtils.makeAssertStatement(treeutils.makeNot(expr.pos, cond), "Illegal assignment to " + expr +
            " conflicting with assiganbles + " + TranslationUtils.assignablesToString(currentAssignable)));
    }

    public JCExpression editAssignable(JCExpression e) {
        if (currentAssignable.stream().anyMatch(loc -> loc instanceof JmlStoreRefKeyword)) {
            if (e instanceof JCIdent) {
                if (!this.ignoreLocals && (((JCIdent) e).sym == null || ((JCIdent) e).sym.owner.equals(currentSymbol))) {
                    if (!loopLocalVars.contains(((JCIdent) e).sym)) {
                        changedLocalVars = changedLocalVars.append(e);
                    }
                }
            }
            return maker.Literal(false);
        }
        if (e instanceof JCIdent) {
            if (!this.ignoreLocals && (((JCIdent) e).sym == null || ((JCIdent) e).sym.owner.equals(currentSymbol))) {
                if (!loopLocalVars.contains(((JCIdent) e).sym)) {
                    changedLocalVars = changedLocalVars.append(e);
                }
                return maker.Literal(false);
            }
            return editAssignable((JCIdent) e);
        } else if (e instanceof JmlStoreRefArrayRange) {
            return editAssignable((JmlStoreRefArrayRange) e);
        } else if (e instanceof JCArrayAccess) {
            JCExpression expr = ((JCArrayAccess) e).indexed;
            if (expr instanceof JCIdent) {
                if (((JCIdent) expr).sym.owner.equals(currentSymbol)) {
                    return maker.Literal(false);
                }
            } else if (expr instanceof JCFieldAccess) {
                if (((JCFieldAccess) expr).sym.owner.equals(currentSymbol)) {
                    return maker.Literal(false);
                }
            }
            return editAssignable((JCArrayAccess) e);
        } else if (e instanceof JCFieldAccess) {
            /*if (((JCFieldAccess) e).sym.owner.equals(currentSymbol) && !params.contains(((JCFieldAccess) e).sym)) {
                return M.Literal(false);
            }*/
            return editAssignable((JCFieldAccess) e);
        } else if (e instanceof JmlStoreRefKeyword) {
            JmlStoreRefKeyword k = (JmlStoreRefKeyword) e;
            if (k.token == JmlTokenKind.BSNOTHING) {
                return maker.Literal(false);
            } else if (k.token == JmlTokenKind.BSEVERYTHING) {
                return maker.Literal(currentAssignable.stream().noneMatch(loc -> loc instanceof JmlStoreRefKeyword));
            } else {
                throw new UnsupportedException("Cannot handle assignment to " + e);
            }
        } else {
            throw new UnsupportedException("Could not handle assignment to " + e.toString());
        }
    }

    public JCExpression editAssignable(JCIdent e) {
        if (e.type.isPrimitive()) {
            if (currentAssignable.stream().filter(as -> as instanceof JCIdent)
                .anyMatch(as -> ((JCIdent) as).sym.equals(e.sym))) {
                return maker.Literal(false);
            }
            if (currentAssignable.stream().filter(as -> as instanceof JCFieldAccess)
                .anyMatch(as -> ((JCFieldAccess) as).sym.equals(e.sym))) {
                return maker.Literal(false);
            }
            return maker.Literal(true);
        } else {
            if (currentAssignable.stream().anyMatch(
                fa -> fa instanceof JCFieldAccess &&
                    ((JCFieldAccess) fa).name == null &&
                    ((JCFieldAccess) fa).selected.toString().equals("this"))) {
                return maker.Literal(false);
            }
            List<JCIdent> pot = List.from(currentAssignable.stream().filter(as -> as instanceof JCIdent)
                .map(as -> (JCIdent) as)
                .filter(as -> !as.type.isPrimitive())
                .filter(as -> isSuperType(as.type, e.type) || isSuperType(e.type, as.type))
                .collect(Collectors.toList()));
            if (pot.size() == 0) {
                return maker.Literal(true);
            }
            JmlMethodInvocation oldExpr = maker.JmlMethodInvocation(JmlTokenKind.BSOLD, pot.get(0));
            forceOld = true;
            JCExpression oldEx = this.copy(oldExpr);
            forceOld = false;
            JCExpression expr = treeutils.makeNeqObject(TranslationUtils.getCurrentPosition(), oldEx, e);
            if (!pot.get(0).sym.owner.equals(currentSymbol) && !pot.get(0).toString().startsWith("this.") && !pot.get(0).toString().equals("this") &&
                !oldVars.containsKey(pot.get(0).toString())) {
                expr = treeutils.makeNeqObject(TranslationUtils.getCurrentPosition(), maker.Ident("this." + pot.get(0)), e);
            }
            for (int i = 1; i < pot.size(); ++i) {
                JmlMethodInvocation oldExpr1 = maker.JmlMethodInvocation(JmlTokenKind.BSOLD, pot.get(i));
                forceOld = true;
                JCExpression oldEx1 = this.copy(oldExpr1);
                forceOld = false;
                if (!pot.get(i).sym.owner.equals(currentSymbol) && !pot.get(i).toString().startsWith("this.") &&
                    !oldVars.containsKey(pot.get(i).toString())) {
                    JCExpression expr1 = treeutils.makeNeqObject(TranslationUtils.getCurrentPosition(), maker.Ident("this." + pot.get(i)), e);
                    expr = treeutils.makeAnd(TranslationUtils.getCurrentPosition(), expr, expr1);
                } else {
                    JCExpression expr1 = treeutils.makeNeqObject(TranslationUtils.getCurrentPosition(), oldEx1, e);
                    expr = treeutils.makeAnd(TranslationUtils.getCurrentPosition(), expr, expr1);
                }
            }
            return expr;
        }
    }

    private boolean isSuperType(Type base, Type sup) {
        if (base.equals(sup)) {
            return true;
        }
        if (!(base instanceof Type.ClassType) || !(sup instanceof Type.ClassType)) {
            return false;
        }
        Type.ClassType b = (Type.ClassType) base;
        return isSuperType(b.supertype_field, sup);
    }

    public JCExpression editAssignable(JCArrayAccess e) {
        List<JmlStoreRefArrayRange> pot = List.from(currentAssignable.stream().filter(as -> as instanceof JmlStoreRefArrayRange)
            .map(arr -> ((JmlStoreRefArrayRange) arr))
            .collect(Collectors.toList()));
        JCExpression expr = editAssignable(e.indexed);
        if (pot.size() == 0) {
            return expr;
        }
        JmlMethodInvocation oldExpr = maker.JmlMethodInvocation(JmlTokenKind.BSOLD, pot.get(0).expression);
        forceOld = true;
        JCExpression oldEx = this.copy(oldExpr);
        forceOld = false;
        JCExpression exprs = treeutils.makeNeqObject(TranslationUtils.getCurrentPosition(), oldEx, e.indexed);
        if (pot.get(0).lo != null || pot.get(0).hi != null) {
            JCExpression hi = pot.get(0).hi;
            JCExpression lo = pot.get(0).lo;
            if (!(hi instanceof JCIdent || hi instanceof JCLiteral || lo instanceof JCIdent || lo instanceof JCLiteral)) {
                throw new UnsupportedException("Only sidecondition free array indices supported. (" + e + ")");
            }
            if (hi == null) {
                hi = treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.MINUS,
                    treeutils.makeArrayLength(TranslationUtils.getCurrentPosition(), pot.get(0).expression), maker.Literal(1));
            }
            if (lo == null) {
                lo = treeutils.makeArrayLength(TranslationUtils.getCurrentPosition(), maker.Literal(0));
            }
            exprs = treeutils.makeOr(TranslationUtils.getCurrentPosition(), exprs,
                treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.GT, e.getIndex(), hi));
            exprs = treeutils.makeOr(TranslationUtils.getCurrentPosition(), exprs,
                treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.LT, e.getIndex(), lo));
        }
        expr = treeutils.makeAnd(TranslationUtils.getCurrentPosition(), expr, exprs);
        for (int i = 1; i < pot.size(); ++i) {
            JmlMethodInvocation oldExpr1 = maker.JmlMethodInvocation(JmlTokenKind.BSOLD, pot.get(i).expression);
            forceOld = true;
            JCExpression oldEx1 = this.copy(oldExpr1);
            forceOld = false;
            JCExpression expr1 = treeutils.makeNeqObject(TranslationUtils.getCurrentPosition(), oldEx1, e.indexed);
            if (pot.get(i).lo != null || pot.get(0).hi != null) {
                JCExpression hi = pot.get(i).hi;
                JCExpression lo = pot.get(i).lo;
                if (hi == null) {
                    hi = treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.MINUS,
                        treeutils.makeArrayLength(TranslationUtils.getCurrentPosition(), pot.get(i).expression), maker.Literal(1));
                }
                if (lo == null) {
                    lo = treeutils.makeArrayLength(TranslationUtils.getCurrentPosition(), maker.Literal(0));
                }
                expr1 = treeutils.makeOr(TranslationUtils.getCurrentPosition(), expr1,
                    treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.GT, e.getIndex(), hi));
                expr1 = treeutils.makeOr(TranslationUtils.getCurrentPosition(), expr1,
                    treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.LT, e.getIndex(), lo));
            }
            expr = treeutils.makeAnd(TranslationUtils.getCurrentPosition(), expr, expr1);
        }
        return expr;
    }

    public JCExpression editAssignable(JmlStoreRefArrayRange e) {
        List<JmlStoreRefArrayRange> pot = List.from(currentAssignable.stream().filter(as -> as instanceof JmlStoreRefArrayRange)
            .map(arr -> ((JmlStoreRefArrayRange) arr))
            .collect(Collectors.toList()));
        JCExpression expr = editAssignable(e.expression);
        if (pot.size() == 0) {
            return expr;
        }
        JmlMethodInvocation oldExpr = maker.JmlMethodInvocation(JmlTokenKind.BSOLD, pot.get(0).expression);
        forceOld = true;
        JCExpression oldEx = this.copy(oldExpr);
        forceOld = false;
        JCExpression exprs = treeutils.makeNeqObject(TranslationUtils.getCurrentPosition(), oldEx, e.expression);
        if (pot.get(0).lo != null || pot.get(0).hi != null) {
            JCExpression hi = pot.get(0).hi;
            JCExpression lo = pot.get(0).lo;
            if (hi == null) {
                hi = treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.MINUS,
                    treeutils.makeArrayLength(TranslationUtils.getCurrentPosition(), pot.get(0).expression), maker.Literal(1));
            }
            if (lo == null) {
                lo = treeutils.makeArrayLength(TranslationUtils.getCurrentPosition(), maker.Literal(0));
            }
            exprs = treeutils.makeOr(TranslationUtils.getCurrentPosition(), exprs,
                treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.GT, e.hi, hi));
            exprs = treeutils.makeOr(TranslationUtils.getCurrentPosition(), exprs,
                treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.LT, e.lo, lo));
        }
        expr = treeutils.makeAnd(TranslationUtils.getCurrentPosition(), expr, exprs);
        for (int i = 1; i < pot.size(); ++i) {
            JCExpression expr1 = treeutils.makeNeqObject(TranslationUtils.getCurrentPosition(), pot.get(i).expression, e.expression);
            if (pot.get(i).lo != null || pot.get(0).hi != null) {
                JCExpression hi = pot.get(i).hi;
                JCExpression lo = pot.get(i).lo;
                if (hi == null) {
                    hi = treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.MINUS,
                        treeutils.makeArrayLength(TranslationUtils.getCurrentPosition(), pot.get(i).expression), maker.Literal(1));
                }
                if (lo == null) {
                    lo = treeutils.makeArrayLength(TranslationUtils.getCurrentPosition(), maker.Literal(0));
                }
                expr1 = treeutils.makeOr(TranslationUtils.getCurrentPosition(), expr1,
                    treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.GT, e.hi, hi));
                expr1 = treeutils.makeOr(TranslationUtils.getCurrentPosition(), expr1,
                    treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.LT, e.lo, lo));
            }
            expr = treeutils.makeAnd(TranslationUtils.getCurrentPosition(), expr, expr1);
        }
        return expr;
    }

    public JCExpression editAssignable(JCFieldAccess f) {
        List<JCFieldAccess> pot = List.from(currentAssignable.stream().filter(as -> as instanceof JCFieldAccess)
            .map(arr -> ((JCFieldAccess) arr))
            .filter(fa -> fa.name == f.name || fa.name == null)
            .collect(Collectors.toList()));
        List<JCIdent> pot1 = List.from(currentAssignable.stream().filter(as -> as instanceof JCIdent)
            .map(arr -> ((JCIdent) arr))
            //.filter(i -> !i.type.isPrimitive())
            .collect(Collectors.toList()));

        JCExpression expr = null;
        if (f.name == null) {
            pot = List.from(currentAssignable.stream().filter(as -> as instanceof JCFieldAccess)
                .map(arr -> ((JCFieldAccess) arr))
                .filter(fa -> fa.name == null)
                .collect(Collectors.toList()));
            if (pot.size() == 0) {
                return maker.Literal(true);
            }
        }
        for (JCFieldAccess fa : pot) {
            if (expr == null) {
                expr = editAssignable(f.selected, fa.selected, true);
            } else {
                expr = treeutils.makeAnd(TranslationUtils.getCurrentPosition(), expr, editAssignable(f.selected, fa.selected, true));
            }

        }
        for (JCIdent i : pot1) {
            JmlMethodInvocation oldExpr = maker.JmlMethodInvocation(JmlTokenKind.BSOLD, i);
            forceOld = true;
            JCExpression oldEx = this.copy(oldExpr);
            forceOld = false;
            if (expr == null) {
                expr = treeutils.makeNeqObject(TranslationUtils.getCurrentPosition(), oldEx, f);
            } else {
                expr = treeutils.makeAnd(TranslationUtils.getCurrentPosition(), expr,
                    treeutils.makeNeqObject(TranslationUtils.getCurrentPosition(), oldEx, f));
            }
        }
        if (expr == null) {
            return maker.Literal(true);
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
        for (JCStatement st : that.getStatements()) {
            newStatements = List.nil();
            JCStatement copy = super.copy(st);
            if (newStatements.size() > 0) {
                l = l.appendList(newStatements);
            } else {
                l = l.append(copy);
            }
        }
        newStatements = orig.append(maker.Block(0L, l));
        return that;
    }

    @Override
    public JCTree visitJmlStatementSpec(JmlStatementSpec that, Void p) {
        throw new UnsupportedException("JmlStatementSpecs not supported. (" + that.toString() + ")");
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
        //if (newStatements.size() > 0) {
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
        ErrorLogger.warn("Blockcontracts are currently not supported (ignored).");
        return null;
    }

    @Override
    public JCTree visitNewClass(NewClassTree node, Void p) {
        JCNewClass newClass = (JCNewClass) node;
        if (newClass.def != null) {
            //anonymous class definition
            ErrorLogger.warn("Anonymous class definitions are only copied currently.");
            List<JCTree> newDefs = List.nil();
            for (JCTree d : newClass.def.defs) {
                if (!(d instanceof JmlMethodDecl)) {
                    newDefs = newDefs.append(d);
                } else {
                    if (!((JmlMethodDecl) d).name.toString().startsWith("<init>")) {
                        newDefs = newDefs.append(d);
                    }
                }
            }
            newClass.def.defs = newDefs;
            return newClass;
        }
        if (BaseVisitor.instance.hasSymbolicVersion(newClass.getIdentifier().toString())) {
            JCExpression ex = maker.Ident(maker.Name(newClass.getIdentifier() + "." + newClass.getIdentifier() + "Symb"));
            ex.setType(newClass.type);
            return maker.App(ex, newClass.args);
        }
        return super.visitNewClass(node, p);
    }

    @Override
    public JCTree visitJmlVariableDecl(JmlVariableDecl that, Void p) {
        JmlVariableDecl copy = (JmlVariableDecl) super.visitJmlVariableDecl(that, p);
        newStatements = newStatements.append(copy);
        loopLocalVars = loopLocalVars.append(copy.sym);
        return copy;
    }

    @Override
    public JCTree visitMethodInvocation(MethodInvocationTree node, Void p) {
        if (translationMode != VerifyFunctionVisitor.TranslationMode.JAVA) {
            if (inConstructor) {
                JCMethodInvocation copy = (JCMethodInvocation) super.visitMethodInvocation(node, p);
                if (copy.meth instanceof JCIdent) {
                    copy.meth = treeutils.makeSelect(TranslationUtils.getCurrentPosition(), maker.Ident(returnVar), ((JCIdent) copy.meth).name);
                }
                return copy;
            }
            //throw new Exceptions.UnsupportedException("Method calls in specifications are currently not supported. (" + node.toString() + ")");
            ErrorLogger.warn("Method calls in specifications only supported experimentally.");
            //  return (JCMethodInvocation)node;
        }
        JCMethodInvocation copy = (JCMethodInvocation) super.visitMethodInvocation(node, p);
        if (CLI.forceInliningMethods) {
            return copy;
        }
        String functionName = "";
        if (copy.meth instanceof JCIdent) {
            functionName = ((JCIdent) copy.meth).name.toString();
        } else if (copy.meth instanceof JCFieldAccess &&
            Objects.equals(copy.meth.type, currentSymbol.owner.type)) {
            functionName = ((JCFieldAccess) copy.meth).name.toString();
        }
        if (BaseVisitor.instance.hasSymbolicVersion(functionName) || copy.meth.toString().equals(currentSymbol.owner.name.toString())) {

            if (currentAssignable.stream().noneMatch(loc -> loc instanceof JmlStoreRefKeyword)) {
                Symbol oldSymbol = currentSymbol;
                if (copy.meth instanceof JCFieldAccess) {
                    currentSymbol = ((JCFieldAccess) copy.meth).sym;
                } else if (copy.meth instanceof JCIdent) {
                    currentSymbol = ((JCIdent) copy.meth).sym;
                } else {
                    throw new TranslationException("method call that could not be handled " + copy.meth.toString());
                }
                List<JCExpression> assignables = BaseVisitor.instance.getAssignablesForName(functionName);
                assert (assignables != null);
                List<JCExpression> newargs = List.nil();
                for (JCExpression e : copy.args) {
                    JCVariableDecl saveParam = treeutils.makeVarDef(e.type, maker.Name("$$param" + paramVarCounter++), oldSymbol,
                        TranslationUtils.getLiteralForType(e.type));
                    neededVariableDefs = neededVariableDefs.append(saveParam);
                    JCAssign a = maker.Assign(maker.Ident(saveParam), this.copy(e));
                    JCStatement assign = maker.Exec(a);
                    CLI.expressionMap.put(a.lhs.toString(), a.rhs.toString());
                    newStatements = newStatements.append(assign);
                    newargs = newargs.append(treeutils.makeIdent(TranslationUtils.getCurrentPosition(), saveParam.sym));
                }
                copy.args = newargs;
                for (JCExpression a : assignables) {
                    JCExpression cond = editAssignable(a, true);
                    cond = treeutils.makeNot(TranslationUtils.getCurrentPosition(), cond);
                    Symbol.MethodSymbol sym = (Symbol.MethodSymbol) ((JCIdent) copy.meth).sym;
                    if (sym.params != null) {
                        for (int i = 0; i < sym.params.length(); ++i) {
                            cond = TranslationUtils.replaceVarName(sym.params.get(i).name.toString(),
                                "$$param" + (paramVarCounter - sym.params.length() + i), cond);
                        }
                    }
                    JCStatement assertion = TranslationUtils.makeAssertStatement(cond,
                            "Illegal assignment to " + a + " conflicting with assignables " +
                                    TranslationUtils.assignablesToString(currentAssignable));
                    assertion.pos = copy.pos;
                    newStatements = newStatements.append(assertion);
                }

                currentSymbol = oldSymbol;
            }
            copy.meth = maker.Ident(copy.meth.toString() + "Symb");

        }

        return copy;
    }

    @Override
    public JCTree visitIf(IfTree node, Void p) {
        List<JCStatement> l = newStatements;
        newStatements = List.nil();
        JCStatement then = super.copy((JCStatement) node.getThenStatement());
        if (newStatements.size() > 1) {
            then = maker.Block(0L, newStatements);
        } else if (newStatements.size() == 1) {
            then = newStatements.get(0);
        }
        newStatements = List.nil();
        JCStatement elseSt = super.copy((JCStatement) node.getElseStatement());
        if (newStatements.size() > 1) {
            elseSt = maker.Block(0L, newStatements);
        } else if (newStatements.size() == 1) {
            elseSt = newStatements.get(0);
        }
        newStatements = List.nil();
        JCExpression cond = super.copy((JCExpression) node.getCondition());
        newStatements = newStatements.appendList(l.append(maker.If(cond, then, elseSt)));
        return (JCIf) node;
    }

    @Override
    public JCTree visitIdentifier(IdentifierTree node, Void p) {
        if (inConstructor && ((JCIdent) node).sym != null && ((JCIdent) node).sym.owner != currentSymbol &&
            !node.getName().toString().equals("this")) {
            return maker.Select(maker.Ident(returnVar), (Name) node.getName());
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
