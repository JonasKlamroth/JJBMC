import com.sun.source.tree.Tree;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.smtlib.impl.Pos;

import java.util.Collections;

import static com.sun.tools.javac.tree.JCTree.*;
import static org.jmlspecs.openjml.JmlTree.*;
import static com.sun.tools.javac.util.List.*;


/**
 * Created by jklamroth on 11/13/18.
 *
 * A utils class which provides several helper methods for the translation.
 */
public class TranslationUtils {
    private static Logger log = LogManager.getLogger(TranslationUtils.class);
    private final Symtab syms;
    private final JmlTreeUtils treeutils;
    private final JmlTree.Maker M;
    private final Names names;

    public TranslationUtils(Context context, JmlTree.Maker maker) {
        this.M = JmlTree.Maker.instance(context);
        this.syms = Symtab.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.names = Names.instance(context);
    }
    static JCTree.JCStatement makeAssumeStatement(JCTree.JCExpression expr, JmlTree.Maker M) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess assumeFunc = M.Select(classCProver, M.Name("assume"));
        JCTree.JCExpression[] args = new JCTree.JCExpression[]{expr};
        com.sun.tools.javac.util.List<JCTree.JCExpression> largs = com.sun.tools.javac.util.List.from(args);
        return M.Exec(
                M.Apply(com.sun.tools.javac.util.List.nil(), assumeFunc, largs));
    }

    static JCTree.JCStatement makeAssertStatement(JCTree.JCExpression expr, JmlTree.Maker M) {
        return M.at(Position.NOPOS).Assert(expr, null);
    }

    static JCExpression getConjunction(List<JCExpression> exprs, Maker M) {
        if(exprs.size() > 0) {
            JCTree.JCExpression ifexpr = exprs.get(0);
            for(int idx = 1; idx < exprs.size(); ++idx) {
                ifexpr = M.Binary(JCTree.Tag.AND, ifexpr, exprs.get(idx));
            }
            return ifexpr;
        }
        return null;
    }

    public JCTree.JCVariableDecl makeNondetIntVar(Name name, Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetInt"));
        List<JCTree.JCExpression> largs = List.nil();
        return treeutils.makeVarDef(syms.intType, name, currentSymbol, M.Apply(List.nil(), nondetFunc, largs));
    }

    public JCTree.JCMethodInvocation makeNondetInt(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetInt"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public JCTree.JCMethodInvocation makeNondetFloat(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetFloat"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public JCTree.JCMethodInvocation makeNondetDouble(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetDouble"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public JCTree.JCMethodInvocation makeNondetLong(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetLong"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public JCTree.JCMethodInvocation makeNondetChar(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetChar"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public JCTree.JCMethodInvocation makeNondetShort(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetShort"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public JCTree.JCMethodInvocation makeNondetWithNull(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetWithNull"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public JCTree.JCMethodInvocation makeNondetBoolean(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetBoolean"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public JCTree.JCStatement makeStandardLoopFromRange(JCTree.JCExpression range, List<JCTree.JCStatement> body, String loopVarName, Symbol currentSymbol, JCExpression init) {
        JCTree.JCVariableDecl loopVar = treeutils.makeVarDef(syms.intType, M.Name(loopVarName), currentSymbol, init);
        RangeExtractor re = new RangeExtractor(M, loopVar.sym);
        re.extractRange(range);
        JCExpression min = re.getMin();
        JCExpression max = re.getMax();
        range = M.Binary(Tag.AND, M.Binary(Tag.LE, min, treeutils.makeIdent(Position.NOPOS, loopVar.sym)), M.Binary(Tag.GE, max, treeutils.makeIdent(Position.NOPOS, loopVar.sym)));
        return makeStandardLoop(range, body, loopVar, currentSymbol);
    }
    public List<JCStatement> replaceVarName(String oldName, String newName, List<JCStatement> expr) {
        for(JCStatement st : expr) {
            ReplaceVisitor.replace(oldName, newName, st, M);
        }
        return expr;
    }
    public JCStatement replaceVarName(String oldName, String newName, JCStatement expr) {
        return ReplaceVisitor.replace(oldName, newName, expr, M);
    }

    public JCExpression replaceVarName(String oldName, String newName, JCExpression expr) {
        return ReplaceVisitor.replace(oldName, newName, expr, M);
    }

    public JCTree.JCStatement makeStandardLoop(JCTree.JCExpression cond, List<JCTree.JCStatement> body, JCTree.JCVariableDecl loopVarName, Symbol currentSymbol) {
        JCTree.JCExpressionStatement loopStep = M.Exec(treeutils.makeUnary(Position.NOPOS, JCTree.Tag.PREINC, treeutils.makeIdent(Position.NOPOS, loopVarName.sym)));
        List<JCTree.JCExpressionStatement> loopStepl = List.from(Collections.singletonList(loopStep));
        JCTree.JCBlock loopBodyBlock = M.Block(0L, List.from(body));
        List<JCTree.JCStatement> loopVarl = List.from(Collections.singletonList(loopVarName));
        return M.ForLoop(loopVarl, cond, loopStepl, loopBodyBlock);
    }

    public JCTree.JCMethodInvocation makeNondetWithoutNull(Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetWithoutNull"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    public JCExpression checkConformAssignables(List<JCExpression> calleeAssignables, List<JCExpression> calledAssignables) {
        if(calledAssignables.size() == 0) {
            return M.Literal(true);
        }
        if(calleeAssignables.size() == 0) {
            return M.Literal(false);
        }
        JCExpression res = null;
        for(JCExpression expr : calledAssignables) {
            JCExpression tmp = null;
            for(JCExpression expr1 : calleeAssignables) {
                if(tmp == null) {
                    tmp = checkConformAssignables(expr, expr1);
                } else {
                    tmp = treeutils.makeBinary(Position.NOPOS, Tag.OR, tmp, checkConformAssignables(expr, expr1));
                }
            }
            if(res == null) {
                res = tmp;
            } else {
                res = treeutils.makeBinary(Position.NOPOS, Tag.AND, res, tmp);
            }
        }
        return res;
    }

    //expr1 < expr2
    private JCExpression checkConformAssignables(JCExpression expr1, JCExpression expr2) {
        Symbol symb1 = null;
        Symbol symb2 = null;
        if(expr1 instanceof JCIdent) {
            symb1 = ((JCIdent) expr1).sym;
        }
        if(expr2 instanceof JCIdent) {
            symb2 = ((JCIdent) expr2).sym;
        }
        if(expr1 instanceof JCFieldAccess) {
            symb1 = ((JCFieldAccess) expr1).sym;
        }
        if(expr2 instanceof JCFieldAccess) {
            symb2 = ((JCFieldAccess) expr2).sym;
        }
        if(expr1 instanceof JmlStoreRefArrayRange && expr2 instanceof  JmlStoreRefArrayRange) {
            JCExpression prev = checkConformAssignables(((JmlStoreRefArrayRange) expr1).expression, ((JmlStoreRefArrayRange) expr2).expression);

            JmlStoreRefArrayRange aexpr1 = (JmlStoreRefArrayRange)expr1;
            JCExpression lo1 = aexpr1.lo;
            JCExpression hi1 = aexpr1.hi;
            if(lo1 == null) {
                lo1 = M.Literal(0);
            }
            if(hi1 == null) {
                hi1 = treeutils.makeBinary(Position.NOPOS, Tag.MINUS, treeutils.makeArrayLength(Position.NOPOS, aexpr1.expression), M.Literal(1));
            }
            JmlStoreRefArrayRange aexpr2 = (JmlStoreRefArrayRange)expr2;
            JCExpression lo2 = aexpr2.lo;
            JCExpression hi2 = aexpr2.hi;
            if(lo2 == null) {
                lo2 = M.Literal(0);
            }
            if(hi2 == null) {
                hi2 = treeutils.makeBinary(Position.NOPOS, Tag.MINUS, treeutils.makeArrayLength(Position.NOPOS, aexpr2.expression), M.Literal(1));
            }
            JCExpression res = treeutils.makeBinary(Position.NOPOS, Tag.GE, lo1, lo2);
            JCExpression res1 = treeutils.makeBinary(Position.NOPOS, Tag.LE, hi1, hi2);
            res = treeutils.makeBinary(Position.NOPOS, Tag.AND, res, res1);
            return treeutils.makeBinary(Position.NOPOS, Tag.AND, res, prev);

        }
        if(symb1 != null && symb2 != null) {
            return treeutils.makeBooleanLiteral(Position.NOPOS, symb1.equals(symb2));
        }
        return treeutils.makeBooleanLiteral(Position.NOPOS, false);
    }

    public List<JCStatement> havoc(List<JCExpression> storerefs, Symbol currentSymbol, JmlTreeCopier jev) {
        List<JCStatement> res = List.nil();
        for(JCExpression expr : storerefs) {
            if(expr instanceof JCIdent) {
                if(((JCIdent) expr).type.isPrimitive()) {
                    res = res.append(M.Exec(M.Assign(expr, getNondetFunctionForType(((JCIdent) expr).type, currentSymbol))));
                } else {
                    res = res.append(M.Exec(M.Assign(expr, makeNondetWithNull(currentSymbol))));
                }
            } else if(expr instanceof  JmlStoreRefArrayRange) {
                JmlStoreRefArrayRange aexpr = (JmlStoreRefArrayRange)expr;
                if(aexpr.hi != null && aexpr.lo != null && aexpr.lo.toString().equals(aexpr.hi.toString())) {
                    Type elemtype = ((Type.ArrayType)aexpr.expression.type).elemtype;
                    JCExpression elemExpr = M.Indexed(aexpr.expression, aexpr.lo);
                    if(elemtype.isPrimitive()) {
                        res = res.append(M.Exec(M.Assign(elemExpr, getNondetFunctionForType(elemtype, currentSymbol))));
                    } else {
                        res = res.append(M.Exec(M.Assign(elemExpr, makeNondetWithNull(currentSymbol))));
                    }
                } else {
                    try {
                        JCExpression lo = aexpr.lo;
                        JCExpression hi = aexpr.hi;
                        if(lo == null) {
                            lo = M.Literal(0);
                        }
                        if(hi == null) {
                            hi = treeutils.makeBinary(Position.NOPOS, Tag.MINUS, treeutils.makeArrayLength(Position.NOPOS, aexpr.expression), M.Literal(1));
                        }
                        JCVariableDecl loopVar = treeutils.makeIntVarDef(M.Name("__tmpVar__"), jev.copy(lo), currentSymbol);
                        JCExpression range = treeutils.makeBinary(Position.NOPOS, Tag.LE, M.Ident(loopVar), jev.copy(hi));
                        JCExpression elemExpr = M.Indexed(aexpr.expression, M.Ident(loopVar));
                        Type elemtype = ((Type.ArrayType)aexpr.expression.type).elemtype;
                        List<JCStatement> body = List.of(M.Exec(M.Assign(elemExpr, getNondetFunctionForType(elemtype, currentSymbol))));
                        res = res.append(makeStandardLoop(range, body, loopVar, currentSymbol));
                    } catch (NumberFormatException e) {
                        throw new RuntimeException("Cant havoc expression " + expr);
                    }
                }
            } else if(expr instanceof JCFieldAccess) {
                JCFieldAccess fexpr = (JCFieldAccess)expr;
                if(fexpr.name == null) {
                    if(fexpr.selected.toString().equals("this")) {
                        throw new RuntimeException("havocing this.* is not supported.");
                    }
                    log.warn("havocing o.* is currently not translated soundly.");
                    res = res.append(M.Exec(M.Assign(fexpr.selected, getNondetFunctionForType(fexpr.selected.type, currentSymbol))));
                } else {
                    res = res.append(M.Exec(M.Assign(expr, getNondetFunctionForType(fexpr.type, currentSymbol))));
                }
            } else if(expr instanceof JmlStoreRefKeyword) {
                if(((JmlStoreRefKeyword) expr).token.equals(JmlTokenKind.BSEVERYTHING)) {
                    log.warn("NOTE: Havoc of \\everything is currently not supported. In method: " + currentSymbol.toString());
                }
            } else {
                throw new RuntimeException("Havoc for expression " + expr + " not supported");
            }
        }
        return res;
    }

    public JCMethodInvocation getNondetFunctionForType(Type type, Symbol currentSymbol, boolean withNull) {
        if(type.equals(syms.intType)) {
            return makeNondetInt(currentSymbol);
        } else if(type.equals(syms.floatType)) {
            return makeNondetFloat(currentSymbol);
        } else if(type.equals(syms.doubleType)) {
            return makeNondetDouble(currentSymbol);
        } else if(type.equals(syms.longType)) {
            return makeNondetLong(currentSymbol);
        } else if(type.equals(syms.shortType)) {
            return makeNondetShort(currentSymbol);
        } else if(type.equals(syms.charType)) {
            return makeNondetChar(currentSymbol);
        } else if(type.equals(syms.booleanType)) {
            return makeNondetBoolean(currentSymbol);
        } else if(type instanceof Type.ArrayType) {
            return makeNondetWithoutNull(currentSymbol);
        } else if(type instanceof Type.ClassType) {
            if(withNull) {
                return makeNondetWithNull(currentSymbol);
            } else {
                return makeNondetWithoutNull(currentSymbol);
            }
        }
        throw new RuntimeException("Nondet for type " + type + " not supported.");
    }

    public JCMethodInvocation getNondetFunctionForType(Type type, Symbol currentSymbol) {
        return getNondetFunctionForType(type, currentSymbol, true);
    }

    public List<JCStatement> diff(List<JCStatement> l1, List<JCStatement> l2) {
        List<JCStatement> res = List.nil();
        for(JCStatement s1 : l1) {
            boolean found = false;
            for(JCStatement s2 : l2) {
                if(s1.toString().equals(s2.toString())) {
                    found = true;
                    break;
                }
            }
            if(!found) {
                res = res.append(s1);
            }
        }
        return res;
    }

    public JCExpression unwrapExpression(JCExpression expr) {
        JCExpression res = expr;
        while(res instanceof JCParens) {
            res = ((JCParens) res).expr;
        }
        return res;
    }

    public List<JCStatement> assumeOrAssertInIf(JCIf ist, JCExpression expr, VerifyFunctionVisitor.TranslationMode transMode) {
        List<JCStatement> newStatements = List.nil();
        if(transMode == VerifyFunctionVisitor.TranslationMode.ASSUME) {
            newStatements = insertIntoIf(ist, makeAssumeStatement(expr, M));
        } else if (transMode == VerifyFunctionVisitor.TranslationMode.ASSERT) {
            newStatements = insertIntoIf(ist, makeAssertStatement(expr, M));
        }
        return newStatements;
    }

    /**
     * Inserts the given Statement into the given ifStatement or returns it in a list if the ifstatement is null
     *
     * @param ist the ifstatement to be inserted to
     * @param statement the statement to be inserted
     * @return the new statements created by this operation
     */
    public List<JCStatement> insertIntoIf(JCIf ist, JCStatement statement) {
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

    public List<JCStatement> insertIntoElse(JCIf ist, JCStatement st) {
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

    public JCStatement makeAssumeOrAssertStatement(JCExpression expr, VerifyFunctionVisitor.TranslationMode mode) {
        if(mode == VerifyFunctionVisitor.TranslationMode.ASSERT) {
            return makeAssertStatement(expr, M);
        } else if(mode == VerifyFunctionVisitor.TranslationMode.ASSUME) {
            return makeAssumeStatement(expr, M);
        }
        throw new RuntimeException("Cant create assume or assert in java mode.");
    }
}

class RangeExtractor extends JmlTreeScanner {
    private JCTree.JCExpression minResult;
    private JCTree.JCExpression maxResult;
    private Symbol ident;
    private final JmlTree.Maker M;

    public RangeExtractor(JmlTree.Maker maker, Symbol ident) {
        this.ident = ident;
        this.M = maker;
    }

    @Override
    public void visitBinary(JCTree.JCBinary tree) {
        if(tree.getKind() == Tree.Kind.GREATER_THAN) {
            if(tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCIdent)tree.getLeftOperand()).name.equals(ident.name)) {
                minResult = M.Binary(JCTree.Tag.PLUS, tree.getRightOperand(), M.Literal(1));
                return;
            }
            if(tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCIdent)tree.getRightOperand()).name.equals(ident.name)) {
                maxResult = M.Binary(Tag.MINUS, tree.getLeftOperand(), M.Literal(1));
                return;
            }
        }
        else if(tree.getKind() == Tree.Kind.LESS_THAN) {
            if(tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent)tree.getLeftOperand()).name.equals(ident.name)) {
                maxResult = M.Binary(Tag.MINUS, tree.getRightOperand(), M.Literal(1));
                return;
            }
            if(tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent)tree.getRightOperand()).name.equals(ident.name)) {
                minResult = M.Binary(Tag.PLUS, tree.getLeftOperand(), M.Literal(1));
                return;
            }
        }
        else if(tree.getKind() == Tree.Kind.GREATER_THAN_EQUAL) {
            if(tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent)tree.getLeftOperand()).name.equals(ident.name)) {
                minResult = tree.getRightOperand();
                return;
            }
            if(tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent)tree.getRightOperand()).name.equals(ident.name)) {
                maxResult = tree.getLeftOperand();
                return;
            }
        }
        else if(tree.getKind() == Tree.Kind.LESS_THAN_EQUAL) {
            if (tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent) tree.getLeftOperand()).name.equals(ident.name)) {
                maxResult = tree.getRightOperand();
                return;
            }
            if (tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent) tree.getRightOperand()).name.equals(ident.name)) {
                minResult = tree.getLeftOperand();
                return;
            }
        }
        super.visitBinary(tree);
    }


    public JCTree.JCExpression getMin() {
        if(minResult == null) {
            throw new RuntimeException("No lower bound for quantified variable found.");
        }
        return minResult;
    }

    public JCTree.JCExpression getMax() {
        if(maxResult == null) {
            throw new RuntimeException("No upper bound for quantified variable found.");
        }
        return maxResult;
    }

    public void extractRange(JCTree tree) {
        super.scan(tree);
        if(maxResult == null || minResult == null) {
            throw new RuntimeException("Could not extract bound from range for expr: " + tree.toString());
        }
    }
}

class ReplaceVisitor extends JmlTreeScanner {
    static String oldName = null;
    static String newName = null;
    private final JmlTree.Maker M;
    public ReplaceVisitor(JmlTree.Maker maker) {
        this.M = maker;
    }
    @Override
    public void visitIdent(JCIdent tree) {
        if(tree.name.toString().equals(oldName)) {
            tree.name = M.Name(newName);
        }
        super.visitIdent(tree);
    }

    @Override
    public void visitVarDef(JCVariableDecl tree) {
        if(tree.name.toString().equals(oldName)) {
            tree.name = M.Name(newName);
        }
        super.visitVarDef(tree);
    }

    public static JCStatement replace(String oldName, String newName, JCStatement expr, Maker maker) {
        ReplaceVisitor.newName = newName;
        ReplaceVisitor.oldName = oldName;
        ReplaceVisitor rv = new ReplaceVisitor(maker);
        rv.scan(expr);
        return expr;
    }

    public static JCExpression replace(String oldName, String newName, JCExpression expr, Maker maker) {
        ReplaceVisitor.newName = newName;
        ReplaceVisitor.oldName = oldName;
        ReplaceVisitor rv = new ReplaceVisitor(maker);
        rv.scan(expr);
        return expr;
    }


}
