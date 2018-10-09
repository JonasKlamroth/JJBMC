import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.*;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;


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

            //System.out.println(api.prettyPrint(rewriteRAC(it, ctx)));
            System.out.println(api.prettyPrint(rewriteAssert(it, ctx)));
        }
    }

    static JCTree rewriteRAC(JmlTree.JmlCompilationUnit cu, Context context) {
        JmlAssertionAdder jaa = new JmlAssertionAdder(context, false, true);
        context.dump();
        return jaa.convert(cu);
    }

    static JCTree rewriteAssert(JmlTree.JmlCompilationUnit cu, Context context) {
        context.dump();
        return cu.accept(new JmlToAssertVisitor(context, JmlTree.Maker.instance(context)), null);
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
}
