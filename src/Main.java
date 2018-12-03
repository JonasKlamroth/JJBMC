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

import java.io.File;


/**
 * @author Alexander Weigl
 * @version 1 (23.07.18)
 * @author jklamroth
 * @version 2 (1.10.18)
 */
public class Main {
    public static final void main(String[] args) throws Exception {
        System.out.println(translate(args));
    }

    static JCTree rewriteRAC(JmlTree.JmlCompilationUnit cu, Context context) {
        JmlAssertionAdder jaa = new JmlAssertionAdder(context, false, true);
        context.dump();
        return jaa.convert(cu);
    }

    static JCTree rewriteAssert(JmlTree.JmlCompilationUnit cu, Context context) {
        context.dump();
        return cu.accept(new BaseVisitor(context, JmlTree.Maker.instance(context)), null);
//        return cu.accept(new JmlToAssertVisitor(context, JmlTree.Maker.instance(context)), null);
    }

    public static String translate(File file) throws Exception {
        String[] args = {file.getAbsolutePath()};
        return translate(args);
    }

    public static String translate(String[] args) throws Exception {
        IAPI api = Factory.makeAPI();
        java.util.List<JmlTree.JmlCompilationUnit> cu = api.parseFiles(args);
        int a = api.typecheck(cu);
        //System.out.printf("a=%d", a);

        Context ctx = api.context();

        for (JmlTree.JmlCompilationUnit it : cu) {
            //System.out.println(api.prettyPrint(rewriteRAC(it, ctx)));
            return api.prettyPrint(rewriteAssert(it, ctx));
        }
        return null;
    }
}