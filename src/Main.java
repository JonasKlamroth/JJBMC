import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.*;
import com.sun.tools.javac.util.List;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.StandardOpenOption;
import java.util.*;


/**
 * @author jklamroth
 * @version 1 (1.10.18)
 */
public class Main {


    public static final void main(String[] args) throws Exception {
        translateAndRunJBMC(args);
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

    public static void translateAndRunJBMC(String[] args) {
        if(args.length < 2) {
            System.out.println("At least two arguments are needed: file and functionName");
            return;
        }
        boolean keepTmpFile = false;
        boolean filterOutput = false;
        int unwinds = -1;
        String fileName = args[0];
        String function = args[1];
        try {
            if(args.length > 2) {
                unwinds = Integer.parseInt(args[2]);
            }
        } catch (NumberFormatException e) {
            System.out.println("Could not parse number of unwinds. Please provide a integer.");
            return;
        }
        File tmpFile = null;
        try {
            File f = new File(fileName);
            if(!f.exists()) {
                System.out.println("Could not find file " + f);
                return;
            }
            String translation = Main.translate(f);
            String name = f.getName().substring(0, f.getName().indexOf("."));
            //TODO This is not always sound!!
            translation = translation.replaceAll(name, name + "tmp");
            tmpFile = new File(f.getParent() + File.separator + name + "tmp.java");
            Files.write(tmpFile.toPath(), translation.getBytes(), StandardOpenOption.CREATE);
        } catch (Exception e) {
            e.printStackTrace();
            return;
        }

        try {
            Runtime rt = Runtime.getRuntime();
            String[] commands = {"javac", "-cp", "." + File.separator + "tests" + File.separator, tmpFile.getPath()};
            Process proc = rt.exec(commands);
            proc.waitFor();


            BufferedReader stdInput = new BufferedReader(new
                    InputStreamReader(proc.getInputStream()));

            BufferedReader stdError = new BufferedReader(new
                    InputStreamReader(proc.getErrorStream()));

            // read the output from the command
            String s = stdInput.readLine();
            if (s != null) {
                System.out.println("Error compiling file: " + tmpFile.getPath());
                while (s != null) {
                    System.out.println(s);
                    s = stdInput.readLine();
                }
                return;
            }
            s = stdError.readLine();
            if (s != null) {
                System.out.println("Error compiling file: " + tmpFile.getPath());
                while (s != null) {
                    System.out.println(s);
                    s = stdError.readLine();
                }
                keepTmpFile = true;
                return;
            }

            function = tmpFile.getName().replace(".java", "") + "." + function;
            System.out.println("Running jbmc for function: " + function);
            //commands = new String[] {"jbmc", tmpFile.getAbsolutePath().replace(".java", ".class")};
            String classFile = tmpFile.getPath().replace(".java", ".class");
            if (unwinds > 0) {
                commands = new String[]{"jbmc", classFile, "--function", function, "--unwind", String.valueOf(unwinds), "--unwinding-assertions"};
            } else {
                commands = new String[]{"jbmc", classFile, "--function", function};
            }

            proc = rt.exec(commands);
            proc.waitFor();

            stdInput = new BufferedReader(new
                    InputStreamReader(proc.getInputStream()));

            stdError = new BufferedReader(new
                    InputStreamReader(proc.getErrorStream()));

            s = stdInput.readLine();
            String out = "";
            if (s != null) {
                out += "JBMC Output for file: " + tmpFile.getPath().replace(".java", ".class") + " with function " + function + "\n";
                while (s != null) {
                    if (!filterOutput || (s.contains("**") || s.contains("FAILURE") || s.contains("VERIFICATION"))) {
                        out += s + "\n";
                    }
                    s = stdInput.readLine();
                }
                s = stdError.readLine();
                while (s != null) {
                    if (!filterOutput || (s.contains("**") || s.contains("FAILURE") || s.contains("VERIFICATION"))) {
                        out += s + "\n";
                    }
                    s = stdError.readLine();
                }
                System.out.println(out);
            }
        } catch (IOException e) {
            System.out.println("Error running jbmc.");
        } catch (InterruptedException e) {
            System.out.println("Error. Jbmc got interrupted.");
        }
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