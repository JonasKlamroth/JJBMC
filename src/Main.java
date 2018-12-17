import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.*;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;

import java.io.File;
import java.io.OutputStream;
import java.io.PrintStream;


/**
 * @author jklamroth
 * @version 1 (1.10.18)
 */
public class Main {
    public static final void main(String[] args) throws Exception {
        String translation = translate(args);
        if(translation != null) {
            System.out.println();
        } else {
            System.out.println("An error occurred during translation.");
        }
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
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
        IAPI api = Factory.makeAPI();
        java.util.List<JmlTree.JmlCompilationUnit> cu = api.parseFiles(args);
        int a = api.typecheck(cu);
        if(a != 0) {
            System.out.println("OpenJml parser Error.");
            return null;
        }
        Context ctx = api.context();


        for (JmlTree.JmlCompilationUnit it : cu) {
            //System.out.println(api.prettyPrint(rewriteRAC(it, ctx)));
            return api.prettyPrint(rewriteAssert(it, ctx));
        }
        return null;
    }

    static class CostumPrintStream extends PrintStream {
        static private boolean filtered = false;

        public CostumPrintStream(OutputStream out) {
            super(out);
        }

        @Override
        public void print(String s) {
            if(!s.startsWith("class ")) {
                super.print(s);
            } else {
                filtered = true;
            }
        }

        @Override
        public void write(byte[] buf, int off, int len) {
            if(!filtered) {
                super.write(buf, off, len);
            } else {
                filtered = false;
            }
        }
    }
}