import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.*;
import org.jmlspecs.openjml.*;


/**
 * @author Alexander Weigl
 * @version 1 (23.07.18)
 */
public class Main {
    public static final void main(String[] args) throws Exception {
        IAPI api = Factory.makeAPI();
        java.util.List<JmlTree.JmlCompilationUnit> cu = api.parseFiles(args);
        int a = api.typecheck(cu);
        System.out.printf("a=%d", a);

        Context ctx = api.context();

        for (JmlTree.JmlCompilationUnit it : cu) {

            System.out.println(api.prettyPrint(rewrite(it, ctx)));
        }
    }

    static JCTree rewrite(JmlTree.JmlCompilationUnit cu, Context context) {
        context.dump();
        return cu.accept(new DefaultReplaceVisitor(context, JmlTree.Maker.instance(context)), null);
    }
}


class RewriteVisitor extends JmlTreeScanner {
    private final JmlTree.Maker M;
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
    private final JmlAttr attr;
    private final Name resultName;
    private final Name exceptionName;
    private final Name exceptionNameCall;
    private final Name terminationName;
    private final ClassReader reader;
    private final Symbol.ClassSymbol utilsClass;
    private final JCTree.JCIdent preLabel;


    RewriteVisitor(Context context) {
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
        this.attr = JmlAttr.instance(context);
        this.resultName = names.fromString(Strings.resultVarString);
        this.exceptionName = names.fromString(Strings.exceptionVarString);
        this.exceptionNameCall = names.fromString(Strings.exceptionCallVarString);
        this.terminationName = names.fromString(Strings.terminationVarString);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
        this.utilsClass = reader.enterClass(names.fromString(Strings.runtimeUtilsFQName));
        this.preLabel = treeutils.makeIdent(Position.NOPOS, Strings.empty, syms.intType);
    }

    @Override
    public void visitBlock(JCTree.JCBlock tree) {
        JCTree.JCIdent classIvil = M.Ident(M.Name("Ivil"));
        JCTree.JCFieldAccess selectIvilSet = M.Select(classIvil, M.Name("set"));

        com.sun.tools.javac.util.List<JCTree.JCStatement> cur = tree.stats;
        while (cur.nonEmpty()) {
            JCTree.JCStatement it = cur.head;
            if (it instanceof JmlTree.JmlStatement) {
                JmlTree.JmlStatement statement = (JmlTree.JmlStatement) it;
                JCTree.JCExpression expr = statement.statement.expr;
                if (expr instanceof JCTree.JCAssign
                        && statement.token == JmlTokenKind.SET) {
                    JCTree.JCAssign jcAssign = (JCTree.JCAssign) expr;
                    JCTree.JCLiteral variable = M.Literal(((JCTree.JCIdent) jcAssign.lhs).name.toString());

                    JCTree.JCExpression args[] = new JCTree.JCExpression[]{variable, jcAssign.rhs};
                    List<JCTree.JCExpression> largs = List.from(args);

                    cur.head =
                            M.at(it.pos).Exec(
                                    M.Apply(com.sun.tools.javac.util.List.nil(), selectIvilSet, largs));
                }
            }
            it.accept(this);
            cur = cur.tail;
        }
    }

    @Override
    public void visitJmlMethodSig(JmlTree.JmlMethodSig that) {
        System.out.println("mtsig = " + that);
        super.visitJmlMethodSig(that);
    }

    @Override
    public void visitJmlMethodSpecs(JmlTree.JmlMethodSpecs tree) {
        System.out.println("ms = " + tree);
        for (JmlTree.JmlSpecificationCase s : tree.forExampleCases) {
            s.accept(this);
        }
        for (JmlTree.JmlSpecificationCase s : tree.impliesThatCases) {
            s.accept(this);
        }
        for (JmlTree.JmlSpecificationCase s : tree.cases) {
            s.accept(this);
        }
        super.visitJmlMethodSpecs(tree);
    }

    @Override
    public void visitJmlSpecificationCase(JmlTree.JmlSpecificationCase tree) {
        super.visitJmlSpecificationCase(tree);
    }

    @Override
    public void visitJmlMethodClauseCallable(JmlTree.JmlMethodClauseCallable tree) {
        System.out.println("mccl = " + tree);
        super.visitJmlMethodClauseCallable(tree);
    }

    @Override
    public void visitJmlMethodClauseConditional(JmlTree.JmlMethodClauseConditional tree) {
        System.out.println("mcc = " + tree);
        super.visitJmlMethodClauseConditional(tree);
    }

    @Override
    public void visitJmlMethodClauseDecl(JmlTree.JmlMethodClauseDecl tree) {
        System.out.println("mcd = " + tree);
        super.visitJmlMethodClauseDecl(tree);
    }

    @Override
    public void visitJmlMethodClauseExpr(JmlTree.JmlMethodClauseExpr tree) {
        System.out.println("mce = " + tree);
        super.visitJmlMethodClauseExpr(tree);
    }

    @Override
    public void visitJmlMethodClauseGroup(JmlTree.JmlMethodClauseGroup tree) {
        System.out.println("mcg = " + tree);
        super.visitJmlMethodClauseGroup(tree);
    }

    @Override
    public void visitJmlMethodClauseSignals(JmlTree.JmlMethodClauseSignals tree) {
        System.out.println("mcs = " + tree);
        super.visitJmlMethodClauseSignals(tree);
    }

    @Override
    public void visitJmlMethodClauseSigOnly(JmlTree.JmlMethodClauseSignalsOnly tree) {
        System.out.println("mcso = " + tree);
        super.visitJmlMethodClauseSigOnly(tree);
    }

    @Override
    public void visitJmlMethodClauseStoreRef(JmlTree.JmlMethodClauseStoreRef tree) {
        System.out.println("mcsr = " + tree);
        super.visitJmlMethodClauseStoreRef(tree);
    }
}
