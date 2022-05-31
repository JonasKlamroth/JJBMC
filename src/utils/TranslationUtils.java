package utils;

import static com.sun.tools.javac.tree.JCTree.JCAnnotation;
import static com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import static com.sun.tools.javac.tree.JCTree.JCBinary;
import static com.sun.tools.javac.tree.JCTree.JCBlock;
import static com.sun.tools.javac.tree.JCTree.JCExpression;
import static com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import static com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import static com.sun.tools.javac.tree.JCTree.JCIdent;
import static com.sun.tools.javac.tree.JCTree.JCIf;
import static com.sun.tools.javac.tree.JCTree.JCLiteral;
import static com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import static com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import static com.sun.tools.javac.tree.JCTree.JCParens;
import static com.sun.tools.javac.tree.JCTree.JCStatement;
import static com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import static com.sun.tools.javac.tree.JCTree.Tag;
import static org.jmlspecs.openjml.JmlTree.JmlAnnotation;
import static org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import static org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import static org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword;
import static org.jmlspecs.openjml.JmlTree.Maker;

import cli.CLI;
import cli.ErrorLogger;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Pair;
import exceptions.TranslationException;
import exceptions.UnsupportedException;
import java.util.Collections;
import java.util.stream.Collectors;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeUtils;
import translation.VerifyFunctionVisitor;


/**
 * Created by jklamroth on 11/13/18.
 *
 * <p>
 * A utils class which provides several helper methods for the translation.
 * </p>
 */
public class TranslationUtils {
    private static final Logger log = LogManager.getLogger(TranslationUtils.class);
    private static final int counter = 0;
    private static Maker M;
    private static Symtab syms;
    private static JmlTreeUtils treeutils;
    private static JmlCompilationUnit compilationUnit;
    private static int currentPosition = -1;

    public static void init(Context context, JmlCompilationUnit compilationUnit) {
        TranslationUtils.M = JmlTree.Maker.instance(context);
        TranslationUtils.syms = Symtab.instance(context);
        TranslationUtils.treeutils = JmlTreeUtils.instance(context);
        TranslationUtils.compilationUnit = compilationUnit;
    }

    public static int getCurrentPosition() {
        return TranslationUtils.currentPosition;
    }

    public static void setCurrentPosition(int pos) {
        TranslationUtils.currentPosition = pos;
    }

    public static void setCurrentASTNode(JCTree node) {
        TranslationUtils.currentPosition = node.getStartPosition();
    }

    public static JCTree.JCStatement makeAssumeStatement(JCTree.JCExpression expr) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess assumeFunc = M.Select(classCProver, M.Name("assume"));
        JCTree.JCExpression[] args = new JCTree.JCExpression[] {expr};
        com.sun.tools.javac.util.List<JCTree.JCExpression> largs = com.sun.tools.javac.util.List.from(args);
        return M.Exec(
            M.Apply(com.sun.tools.javac.util.List.nil(), assumeFunc, largs));
    }


    static List<JCTree.JCStatement> makeAssertStatementList(JCTree.JCExpression expr, String info) {
        if (CLI.splitAssertions) {
            expr = unwrapExpression(expr);
            if (expr instanceof JCBinary) {
                JCBinary binary = (JCBinary) expr;
                if (binary.opcode == Tag.AND) {
                    List<JCStatement> l = List.nil();
                    l = l.appendList(makeAssertStatementList(binary.lhs));
                    l = l.appendList(makeAssertStatementList(binary.rhs));
                    return l;
                }
            }
        }
        if (info != null) {
            return List.of(M.at(TranslationUtils.getCurrentPosition()).Assert(expr, M.Literal(info)));
        }
        return List.of(M.at(TranslationUtils.getCurrentPosition()).Assert(expr, null));
    }

    static List<JCTree.JCStatement> makeAssertStatementList(JCExpression expr) {
        return makeAssertStatementList(expr, null);
    }

    public static JCStatement makeAssertStatement(JCExpression expr, String info) {
        List<JCStatement> l = makeAssertStatementList(expr, info);
        if (l.size() == 1) {
            return l.get(0);
        }
        return M.Block(0L, l);
    }

    public static JCStatement makeAssertStatement(JCExpression expr) {
        return makeAssertStatement(expr, null);
    }

    static JCExpression getConjunction(List<JCExpression> exprs) {
        if (exprs.size() > 0) {
            JCTree.JCExpression ifexpr = exprs.get(0);
            for (int idx = 1; idx < exprs.size(); ++idx) {
                ifexpr = M.Binary(JCTree.Tag.AND, ifexpr, exprs.get(idx));
            }
            return ifexpr;
        }
        return null;
    }

    public static JCTree.JCVariableDecl makeNondetIntVar(Name name, Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetInt"));
        List<JCTree.JCExpression> largs = List.nil();
        return treeutils.makeVarDef(syms.intType, name, currentSymbol, M.Apply(List.nil(), nondetFunc, largs));
    }

    public static JCTree.JCMethodInvocation makeNondetInt(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetInt"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public static JCTree.JCMethodInvocation makeNondetFloat(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetFloat"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public static JCTree.JCMethodInvocation makeNondetDouble(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetDouble"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public static JCTree.JCMethodInvocation makeNondetLong(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetLong"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public static JCTree.JCMethodInvocation makeNondetChar(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetChar"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public static JCTree.JCMethodInvocation makeNondetShort(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetShort"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public static JCTree.JCMethodInvocation makeNondetWithNull(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetWithNull"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public static JCTree.JCMethodInvocation makeNondetBoolean(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetBoolean"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public static JCTree.JCForLoop makeStandardLoopFromRange(JCTree.JCExpression range, List<JCTree.JCStatement> body, String loopVarName,
                                                             Symbol currentSymbol, JCExpression init) {
        JCTree.JCVariableDecl loopVar = treeutils.makeVarDef(syms.intType, M.Name(loopVarName), currentSymbol, init);
        RangeExtractor re = new RangeExtractor(M, loopVar.sym);
        re.extractRange(range);
        JCExpression min = re.getMin();
        JCExpression max = re.getMax();
        range = M.Binary(Tag.AND, M.Binary(Tag.LE, min, treeutils.makeIdent(TranslationUtils.getCurrentPosition(), loopVar.sym)),
            M.Binary(Tag.GE, max, treeutils.makeIdent(TranslationUtils.getCurrentPosition(), loopVar.sym)));
        return makeStandardLoop(range, body, loopVar, currentSymbol);
    }

    public static List<JCStatement> replaceVarName(String oldName, String newName, List<JCStatement> expr) {
        List<JCStatement> res = List.nil();
        for (int i = 0; i < expr.size(); ++i) {
            res = res.append(ReplaceVisitor.replace(oldName, newName, expr.get(i), M));
        }
        return res;
    }

    public static JCStatement replaceVarName(String oldName, String newName, JCStatement expr) {
        return ReplaceVisitor.replace(oldName, newName, expr, M);
    }

    public static JCExpression replaceVarName(String oldName, String newName, JCExpression expr) {
        return ReplaceVisitor.replace(oldName, newName, expr, M);
    }

    public static JCTree.JCForLoop makeStandardLoop(JCTree.JCExpression cond, List<JCTree.JCStatement> body, JCTree.JCVariableDecl loopVarName,
                                                    Symbol currentSymbol) {
        JCTree.JCExpressionStatement loopStep = M.Exec(treeutils.makeUnary(TranslationUtils.getCurrentPosition(), JCTree.Tag.PREINC,
            treeutils.makeIdent(TranslationUtils.getCurrentPosition(), loopVarName.sym)));
        List<JCTree.JCExpressionStatement> loopStepl = List.from(Collections.singletonList(loopStep));
        JCTree.JCBlock loopBodyBlock = M.Block(0L, List.from(body));
        List<JCTree.JCStatement> loopVarl = List.from(Collections.singletonList(loopVarName));
        return M.ForLoop(loopVarl, cond, loopStepl, loopBodyBlock);
    }

    public static JCTree.JCMethodInvocation makeNondetWithoutNull(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetWithoutNull"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public static JCExpression checkConformAssignables(List<JCExpression> calleeAssignables, List<JCExpression> calledAssignables) {
        if (calledAssignables.size() == 0) {
            return M.Literal(true);
        }
        if (calleeAssignables.size() == 0) {
            return M.Literal(false);
        }
        JCExpression res = null;
        for (JCExpression expr : calledAssignables) {
            JCExpression tmp = null;
            for (JCExpression expr1 : calleeAssignables) {
                if (tmp == null) {
                    tmp = checkConformAssignables(expr, expr1);
                } else {
                    tmp = treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.OR, tmp, checkConformAssignables(expr, expr1));
                }
            }
            if (res == null) {
                res = tmp;
            } else {
                res = treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.AND, res, tmp);
            }
        }
        return res;
    }

    //expr1 < expr2
    private static JCExpression checkConformAssignables(JCExpression expr1, JCExpression expr2) {
        Symbol symb1 = null;
        Symbol symb2 = null;
        if (expr1 instanceof JCIdent) {
            symb1 = ((JCIdent) expr1).sym;
        }
        if (expr2 instanceof JCIdent) {
            symb2 = ((JCIdent) expr2).sym;
        }
        if (expr1 instanceof JCFieldAccess) {
            symb1 = ((JCFieldAccess) expr1).sym;
        }
        if (expr2 instanceof JCFieldAccess) {
            symb2 = ((JCFieldAccess) expr2).sym;
        }
        if (expr1 instanceof JmlStoreRefArrayRange && expr2 instanceof JmlStoreRefArrayRange) {
            JCExpression prev = checkConformAssignables(((JmlStoreRefArrayRange) expr1).expression, ((JmlStoreRefArrayRange) expr2).expression);

            JmlStoreRefArrayRange aexpr1 = (JmlStoreRefArrayRange) expr1;
            JCExpression lo1 = aexpr1.lo;
            JCExpression hi1 = aexpr1.hi;
            if (lo1 == null) {
                lo1 = M.Literal(0);
            }
            if (hi1 == null) {
                hi1 = treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.MINUS,
                    treeutils.makeArrayLength(TranslationUtils.getCurrentPosition(), aexpr1.expression), M.Literal(1));
            }
            JmlStoreRefArrayRange aexpr2 = (JmlStoreRefArrayRange) expr2;
            JCExpression lo2 = aexpr2.lo;
            JCExpression hi2 = aexpr2.hi;
            if (lo2 == null) {
                lo2 = M.Literal(0);
            }
            if (hi2 == null) {
                hi2 = treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.MINUS,
                    treeutils.makeArrayLength(TranslationUtils.getCurrentPosition(), aexpr2.expression), M.Literal(1));
            }
            JCExpression res = treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.GE, lo1, lo2);
            JCExpression res1 = treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.LE, hi1, hi2);
            res = treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.AND, res, res1);
            return treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.AND, res, prev);

        }
        if (symb1 != null && symb2 != null) {
            return treeutils.makeBooleanLiteral(TranslationUtils.getCurrentPosition(), symb1.equals(symb2));
        }
        return treeutils.makeBooleanLiteral(TranslationUtils.getCurrentPosition(), false);
    }

    public static List<JCStatement> havoc(List<? extends JCExpression> storerefs, Symbol currentSymbol, JmlTreeCopier jev) {
        List<JCStatement> res = List.nil();
        List<String> havoced = List.nil();
        for (JCExpression expr : storerefs) {
            if (!havoced.contains((expr.toString()))) {
                havoced = havoced.append(expr.toString());
                if (expr instanceof JCIdent) {
                    if (expr.type.isPrimitive()) {
                        res = res.append(M.Exec(M.Assign(expr, getNondetFunctionForType(expr.type, currentSymbol))));
                    } else {
                        res = res.append(M.Exec(M.Assign(expr, makeNondetWithNull(currentSymbol))));
                    }
                } else if (expr instanceof JmlStoreRefArrayRange) {
                    JmlStoreRefArrayRange arrayRange = (JmlStoreRefArrayRange) expr;
                    Type elemType = ((Type.ArrayType) arrayRange.expression.type).elemtype;
                    JCExpression inner = expr;
                    List<Pair<JCExpression, JCExpression>> dims = List.nil();
                    List<JCVariableDecl> loopVars = List.nil();
                    int idx = 0;
                    while (inner instanceof JmlStoreRefArrayRange) {
                        dims = dims.append(new Pair<>(((JmlStoreRefArrayRange) inner).lo, ((JmlStoreRefArrayRange) inner).hi));
                        loopVars =
                            loopVars.append(treeutils.makeIntVarDef(M.Name("__tmpVar__" + idx++), ((JmlStoreRefArrayRange) inner).lo, currentSymbol));
                        inner = ((JmlStoreRefArrayRange) inner).expression;
                    }
                    List<JCExpression> expressions = List.nil();
                    JCExpression finalExpression = inner;
                    for (int i = loopVars.size() - 1; i >= 0; --i) {
                        expressions = expressions.prepend(finalExpression);
                        finalExpression = M.Indexed(finalExpression, M.Ident(loopVars.get(i)));
                    }
                    if (dims.size() == 1) {
                        if (dims.get(0).fst != null && dims.get(0).fst.toString().equals(dims.get(0).snd.toString())) {
                            JCExpression arrayAccess = M.Indexed(inner, dims.get(0).fst);
                            JCStatement body = M.Exec(M.Assign(arrayAccess, getNondetFunctionForType(elemType, currentSymbol)));
                            res = res.append(body);
                            continue;
                        }
                    }

                    JCStatement body = M.Exec(M.Assign(finalExpression, getNondetFunctionForType(elemType, currentSymbol)));
                    for (int i = 0; i < dims.size(); ++i) {
                        try {
                            Pair<JCExpression, JCExpression> d = dims.get(i);
                            JCVariableDecl loopVar = loopVars.get(i);
                            JCExpression lo = d.fst;
                            JCExpression hi = d.snd;
                            if (lo == null) {
                                lo = M.Literal(0);
                                loopVar.init = lo;
                            }
                            if (hi == null) {
                                hi = treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.MINUS,
                                    treeutils.makeArrayLength(TranslationUtils.getCurrentPosition(), expressions.get(i)), M.Literal(1));
                            }
                            JCExpression range = treeutils.makeBinary(TranslationUtils.getCurrentPosition(), Tag.LE, M.Ident(loopVar), jev.copy(hi));
                            JCStatement ifst = M.If(
                                treeutils.makeNeqObject(TranslationUtils.getCurrentPosition(), expressions.get(i), treeutils.nullLit),
                                M.Block(0L, List.of(makeStandardLoop(range, List.of(body), loopVar, currentSymbol))),
                                null
                            );
                            body = ifst;
                        } catch (NumberFormatException e) {
                            throw new TranslationException("Cant havoc expression " + expr);
                        }
                    }
                    res = res.append(body);
                } else if (expr instanceof JCFieldAccess) {
                    JCFieldAccess fexpr = (JCFieldAccess) expr;
                    if (fexpr.name == null) {
                        if (fexpr.selected.toString().equals("this")) {
                            throw new UnsupportedException("havocing this.* is not supported.");
                        }
                        ErrorLogger.warn("havocing o.* is currently not translated soundly.");
                        res = res.append(M.Exec(M.Assign(fexpr.selected, getNondetFunctionForType(fexpr.selected.type, currentSymbol))));
                    } else {
                        res = res.append(M.Exec(M.Assign(expr, getNondetFunctionForType(fexpr.type, currentSymbol))));
                    }
                } else if (expr instanceof JmlStoreRefKeyword) {
                    if (((JmlStoreRefKeyword) expr).token.equals(JmlTokenKind.BSEVERYTHING)) {
                        log.warn("NOTE: Havoc of \\everything is currently not supported. In method: " + currentSymbol.toString());
                    }
                } else {
                    throw new UnsupportedException("Havoc for expression " + expr + " not supported");
                }
            }
        }
        return res;
    }

    public static JCLiteral getLiteralForType(Type t) {
        if (t.getTag().equals(TypeTag.INT)) {
            return M.Literal(0);
        }
        if (t.getTag().equals(TypeTag.LONG)) {
            return M.Literal(0);
        }
        if (t.getTag().equals(TypeTag.DOUBLE)) {
            return M.Literal(0.0);
        }
        if (t.getTag().equals(TypeTag.FLOAT)) {
            return M.Literal(0.0f);
        }
        if (t.getTag().equals(TypeTag.SHORT)) {
            return M.Literal(0);
        }
        if (t.getTag().equals(TypeTag.BOOLEAN)) {
            return M.Literal(true);
        }
        if (t.getTag().equals(TypeTag.CHAR)) {
            return M.Literal(0);
        }
        return treeutils.nullLit;
    }

    public static JCMethodInvocation getNondetFunctionForType(Type type, Symbol currentSymbol, boolean withNull) {
        if (type instanceof Type.AnnotatedType) {
            log.warn("Type annotations are currently being ignored! (nullable is the default for this tool)");
            type = type.unannotatedType();
        }
        if (type.equals(syms.intType)) {
            return makeNondetInt(currentSymbol);
        } else if (type.equals(syms.floatType)) {
            return makeNondetFloat(currentSymbol);
        } else if (type.equals(syms.doubleType)) {
            return makeNondetDouble(currentSymbol);
        } else if (type.equals(syms.longType)) {
            return makeNondetLong(currentSymbol);
        } else if (type.equals(syms.shortType)) {
            return makeNondetShort(currentSymbol);
        } else if (type.equals(syms.charType)) {
            return makeNondetChar(currentSymbol);
        } else if (type.equals(syms.booleanType)) {
            return makeNondetBoolean(currentSymbol);
        } else if (type instanceof Type.ArrayType) {
            return makeNondetWithoutNull(currentSymbol);
        } else if (type instanceof Type.ClassType) {
            if (withNull) {
                return makeNondetWithNull(currentSymbol);
            } else {
                return makeNondetWithoutNull(currentSymbol);
            }
        }
        throw new UnsupportedException("Nondet for type " + type + " not supported.");
    }

    public static JCMethodInvocation getNondetFunctionForType(Type type, Symbol currentSymbol) {
        return getNondetFunctionForType(type, currentSymbol, true);
    }

    public static List<JCStatement> diff(List<JCStatement> l1, List<JCStatement> l2) {
        List<JCStatement> res = List.nil();
        for (JCStatement s1 : l1) {
            boolean found = false;
            for (JCStatement s2 : l2) {
                if (s1.toString().equals(s2.toString())) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                res = res.append(s1);
            }
        }
        return res;
    }

    public static JCExpression unwrapExpression(JCExpression expr) {
        JCExpression res = expr;
        while (res instanceof JCParens) {
            res = ((JCParens) res).expr;
        }
        return res;
    }

    public static List<JCStatement> assumeOrAssertInif(JCIf ist, JCExpression expr, VerifyFunctionVisitor.TranslationMode transMode) {
        List<JCStatement> newStatements = List.nil();
        if (transMode == VerifyFunctionVisitor.TranslationMode.ASSUME) {
            newStatements = insertIntoif(ist, makeAssumeStatement(expr));
        } else if (transMode == VerifyFunctionVisitor.TranslationMode.ASSERT) {
            newStatements = insertIntoif(ist, makeAssertStatement(expr));
        }
        return newStatements;
    }

    /**
     * Inserts the given statement into the given ifStatement or returns it in a list of the ifstatement is null.
     *
     * @param ist       the ifstatement to be inserted to
     * @param statement the statement to be inserted
     * @return the new statements created by this operation
     */
    public static List<JCStatement> insertIntoif(JCIf ist, JCStatement statement) {
        List<JCStatement> newStatements = List.nil();
        if (ist != null) {
            if (ist.thenpart == null) {
                ist.thenpart = statement;
            } else if (ist.thenpart instanceof JCBlock) {
                ((JCBlock) ist.thenpart).stats = ((JCBlock) ist.thenpart).stats.append(statement);
            } else {
                ist.thenpart = M.Block(0L, List.of(ist.thenpart).append(statement));
            }
        } else {
            newStatements = newStatements.append(statement);
        }
        return newStatements;
    }

    public static List<JCStatement> insertIntoElse(JCIf ist, JCStatement st) {
        List<JCStatement> newStatements = List.nil();
        if (ist != null) {
            if (ist.elsepart == null) {
                ist.elsepart = st;
            } else if (ist.elsepart instanceof JCBlock) {
                ((JCBlock) ist.elsepart).stats = ((JCBlock) ist.elsepart).stats.append(st);
            } else {
                ist.elsepart = M.Block(0L, List.of(ist.elsepart).append(st));
            }
        } else {
            newStatements = newStatements.append(st);
        }
        return newStatements;
    }

    public static JCStatement makeAssumeOrAssertStatement(JCExpression expr, VerifyFunctionVisitor.TranslationMode mode) {
        if (mode == VerifyFunctionVisitor.TranslationMode.ASSERT) {
            return makeAssertStatement(expr);
        } else if (mode == VerifyFunctionVisitor.TranslationMode.ASSUME) {
            return makeAssumeStatement(expr);
        }
        throw new TranslationException("Cant create assume or assert in java mode.");
    }

    public static boolean isAssumeStatement(JCStatement jcStatement) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess assumeFunc = M.Select(classCProver, M.Name("assume"));
        //JCTree.JCExpression[] args = new JCTree.JCExpression[]{expr};
        //com.sun.tools.javac.util.List<JCTree.JCExpression> largs = com.sun.tools.javac.util.List.from(args);
        //return M.Exec(
        //M.Apply(com.sun.tools.javac.util.List.nil(), assumeFunc, largs));

        if (!(jcStatement instanceof JCExpressionStatement)) {
            return false;
        }
        JCExpressionStatement exprStmt = (JCExpressionStatement) jcStatement;
        if (!(exprStmt.expr instanceof JCMethodInvocation)) {
            return false;
        }
        JCMethodInvocation method = (JCMethodInvocation) exprStmt.expr;
        if (!(method.meth instanceof JCFieldAccess)) {
            return false;
        }
        JCFieldAccess fa = (JCFieldAccess) method.meth;
        return fa.name.toString().equals("assume") && fa.selected.toString().equals("CProver");
    }

    public static JCExpression extractAssumeExpr(JCStatement jcStatement) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess assumeFunc = M.Select(classCProver, M.Name("assume"));
        //JCTree.JCExpression[] args = new JCTree.JCExpression[]{expr};
        //com.sun.tools.javac.util.List<JCTree.JCExpression> largs = com.sun.tools.javac.util.List.from(args);
        //return M.Exec(
        //M.Apply(com.sun.tools.javac.util.List.nil(), assumeFunc, largs));

        if (!(jcStatement instanceof JCExpressionStatement)) {
            return null;
        }
        JCExpressionStatement exprStmt = (JCExpressionStatement) jcStatement;
        if (!(exprStmt.expr instanceof JCMethodInvocation)) {
            return null;
        }
        JCMethodInvocation method = (JCMethodInvocation) exprStmt.expr;
        if (!(method.meth instanceof JCFieldAccess)) {
            return null;
        }
        JCFieldAccess fa = (JCFieldAccess) method.meth;
        if (fa.name.toString().equals("assume") && fa.selected.toString().equals("CProver")) {
            return method.args.get(0);
        }
        return null;
    }

    public static List<JCExpression> filterAssignables(List<JCExpression> assignables) {
        if (assignables.contains(M.JmlStoreRefKeyword(JmlTokenKind.BSEVERYTHING))) {
            return List.of(M.JmlStoreRefKeyword(JmlTokenKind.BSEVERYTHING));
        }
        List<JCExpression> res = List.nil();
        List<JCExpression> jmlArrayRanges =
            List.from(assignables.stream().filter(e -> e instanceof JmlStoreRefArrayRange).collect(Collectors.toList()));
        jmlArrayRanges = List.from(jmlArrayRanges.stream().sorted((l, r) -> l.toString().contains("*") ? -1 : 1).collect(Collectors.toList()));
        for (JCExpression e : jmlArrayRanges) {
            JmlStoreRefArrayRange range = (JmlStoreRefArrayRange) e;
            if (range.hi == null && range.lo == null) {
                res = res.append(range);
            } else {
                if (!res.stream()
                    .anyMatch(r -> r instanceof JmlStoreRefArrayRange && ((JmlStoreRefArrayRange) r).expression.equals(range.expression))) {
                    res = res.append(range);
                }
            }
        }

        List<JCExpression> arrayRanges = List.from(assignables.stream().filter(e -> e instanceof JCArrayAccess).collect(Collectors.toList()));
        arrayRanges = List.from(arrayRanges.stream().sorted((l, r) -> l.toString().contains("*") ? -1 : 1).collect(Collectors.toList()));
        for (JCExpression e : arrayRanges) {
            JCArrayAccess range = (JCArrayAccess) e;
            if (!res.stream().anyMatch(
                r -> r instanceof JmlStoreRefArrayRange && ((JmlStoreRefArrayRange) r).expression.toString().equals(range.indexed.toString()))) {
                res = res.append(range);
            }
        }

        List<JCExpression> fields = List.from(assignables.stream().filter(e -> e instanceof JCFieldAccess).collect(Collectors.toList()));
        fields = List.from(fields.stream().sorted((l, r) -> ((JCFieldAccess) l).name == null ? -1 : 1).collect(Collectors.toList()));
        for (JCExpression e : fields) {
            JCFieldAccess field = (JCFieldAccess) e;
            if (field.name == null) {
                res = res.append(field);
            } else {
                if (!res.stream()
                    .anyMatch(r -> r instanceof JCFieldAccess && ((JCFieldAccess) r).selected.toString().equals(field.selected.toString()))) {
                    res = res.append(field);
                }
            }
        }
        List<JCExpression> rest = List.from(
            assignables.stream().filter(e -> !(e instanceof JCFieldAccess) && !(e instanceof JmlStoreRefArrayRange) && !(e instanceof JCArrayAccess))
                .collect(Collectors.toList()));
        res = res.appendList(rest);
        return res;
    }

    public static boolean isPure(JCMethodDecl meth) {
        if (meth.mods.annotations != null) {
            for (JCAnnotation a : meth.mods.annotations) {
                if (a instanceof JmlAnnotation) {
                    if (a.annotationType.toString().endsWith(".Pure")) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    public static int getLineNumber(JCTree node) {
        return compilationUnit.getLineMap().getLineNumber(node.getStartPosition());
    }

    public static String getPackageName() {
        JCExpression packageName = compilationUnit.getPackageName();
        return packageName == null ? "" : packageName.toString();
    }
}
