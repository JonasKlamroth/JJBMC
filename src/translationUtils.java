import com.sun.source.tree.Tree;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.parser.Tokens;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Utils;

import java.util.Collections;

/**
 * Created by jklamroth on 11/13/18.
 */
public class translationUtils {
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
    private final JmlTree.Maker M;

    public translationUtils(Context context, JmlTree.Maker maker) {
        this.context = context;
        this.log = Log.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.nowarns = Nowarns.instance(context);
        this.syms = Symtab.instance(context);
        this.types = Types.instance(context);
        this.utils = Utils.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.jmltypes = JmlTypes.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
    }
    static JCTree.JCStatement makeAssumeStatement(JCTree.JCExpression expr, JmlTree.Maker M) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess assumeFunc = M.Select(classCProver, M.Name("assume"));
        JCTree.JCExpression args[] = new JCTree.JCExpression[]{expr};
        com.sun.tools.javac.util.List<JCTree.JCExpression> largs = com.sun.tools.javac.util.List.from(args);
        return M.Exec(
                M.Apply(com.sun.tools.javac.util.List.nil(), assumeFunc, largs));
    }

    static JCTree.JCStatement makeAssertStatement(JCTree.JCExpression expr, JmlTree.Maker M, List<JCTree.JCExpression> assumptions) {
        if(assumptions.size() > 0) {
            JCTree.JCExpression ifexpr = assumptions.get(0);
            for(int idx = 1; idx < assumptions.size(); ++idx) {
                ifexpr = M.Binary(JCTree.Tag.AND, ifexpr, assumptions.get(idx));
            }
            return M.If(ifexpr, M.at(Position.NOPOS).Assert(expr, null), null);
        }
        return M.at(Position.NOPOS).Assert(expr, null);
    }

    static JCTree.JCStatement makeAssertStatement(JCTree.JCExpression expr, JmlTree.Maker M) {
        return makeAssertStatement(expr, M, List.nil());
    }

    public JCTree.JCVariableDecl makeNondetIntVar(Name name, Symbol currentSymbol) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetInt"));
        List<JCTree.JCExpression> largs = List.nil();
        JCTree.JCVariableDecl quantVar = treeutils.makeVarDef(syms.intType, name, currentSymbol, M.Apply(List.nil(), nondetFunc, largs));
        return quantVar;
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

    public JCTree.JCStatement makeStandardLoop(JCTree.JCExpression range, List<JCTree.JCStatement> body, JCTree.JCVariableDecl loopVarName, Symbol currentSymbol) {
        RangeExtractor re = new RangeExtractor(M, loopVarName.sym);
        re.scan(range);
        JCTree.JCVariableDecl loopVar = treeutils.makeVarDef(syms.intType, loopVarName.name, currentSymbol, re.getMin());
        JCTree.JCExpression loopCond = range;
        JCTree.JCExpressionStatement loopStep = M.Exec(treeutils.makeUnary(Position.NOPOS, JCTree.Tag.PREINC, treeutils.makeIdent(Position.NOPOS, loopVar.sym)));
        List<JCTree.JCExpressionStatement> loopStepl = List.from(Collections.singletonList(loopStep));
        JCTree.JCBlock loopBodyBlock = M.Block(0L, List.from(body));
        List<JCTree.JCStatement> loopVarl = List.from(Collections.singletonList(loopVar));
        return M.ForLoop(loopVarl, loopCond, loopStepl, loopBodyBlock);
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
            if(tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent)tree.getLeftOperand()).sym.equals(ident)) {
                minResult = M.Binary(JCTree.Tag.PLUS, tree.getRightOperand(), M.Literal(1));
            }
            if(tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent)tree.getRightOperand()).sym.equals(ident)) {
                maxResult = M.Binary(JCTree.Tag.PLUS, tree.getLeftOperand(), M.Literal(1));
            }
        }
        if(tree.getKind() == Tree.Kind.LESS_THAN) {
            if(tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent)tree.getLeftOperand()).sym.equals(ident)) {
                maxResult = M.Binary(JCTree.Tag.PLUS, tree.getRightOperand(), M.Literal(1));
            }
            if(tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent)tree.getRightOperand()).sym.equals(ident)) {
                minResult = M.Binary(JCTree.Tag.PLUS, tree.getLeftOperand(), M.Literal(1));
            }
        }
        if(tree.getKind() == Tree.Kind.GREATER_THAN_EQUAL) {
            if(tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent)tree.getLeftOperand()).sym.equals(ident)) {
                minResult = tree.getRightOperand();
            }
            if(tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent)tree.getRightOperand()).sym.equals(ident)) {
                maxResult = tree.getLeftOperand();
            }
        }
        if(tree.getKind() == Tree.Kind.LESS_THAN_EQUAL) {
            if(tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent)tree.getLeftOperand()).sym.equals(ident)) {
                maxResult = tree.getRightOperand();
            }
            if(tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent)tree.getRightOperand()).sym.equals(ident)) {
                minResult = tree.getLeftOperand();
            }
        }
        super.visitBinary(tree);
    }

    public JCTree.JCExpression getMin() {
        return minResult;
    }

    public JCTree.JCExpression getMax() {
        return maxResult;
    }
}