import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.Factory;
import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.junit.After;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Created by jklamroth on 12/3/18.
 */
public class TestExecutor {

    static String[] fileNames = {"./tests/TestSuite.java"};
    private File tmpFile = new File("./tests/tmp.java");
    private boolean keepTmpFile = true;
    private boolean filterOutput = false;
    private boolean doCleanup = false;

    @org.junit.Test
    public void runBubbleSortCaseStudy() throws IOException, InterruptedException {
        fileNames = new String[]{"./tests/CaseStudy/BubbleSortSymb.java"};
        testTranslation();
    }

    @org.junit.Test
    public void testTranslation() throws IOException, InterruptedException {
        for(String fileName : fileNames) {

            try {
                File f = new File(fileName);
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
                assertTrue("Error compiling file " + fileName, false);
                return;
            }
            s = stdError.readLine();
            if (s != null) {
                System.out.println("Error compiling file: " + tmpFile.getPath());
                while (s != null) {
                    System.out.println(s);
                    s = stdError.readLine();
                }
                assertTrue("Error compiling file " + tmpFile, false);
                keepTmpFile = true;
                return;
            }

            FunctionNameVisitor.parseFile(tmpFile.getPath());
            List<FunctionNameVisitor.TestBehaviour> testBehaviours = FunctionNameVisitor.functionBehaviours;
            List<String> functionNames = FunctionNameVisitor.functionNames;
            List<String> unwinds = FunctionNameVisitor.unwinds;
            assertEquals(functionNames.size(), testBehaviours.size());
            assertEquals(functionNames.size(), unwinds.size());
            int idx = 0;
            for(String function : functionNames) {
                if(testBehaviours.get(idx) != FunctionNameVisitor.TestBehaviour.Ignored) {
                    System.out.println("Running test for function: " + function);
                    //commands = new String[] {"jbmc", tmpFile.getAbsolutePath().replace(".java", ".class")};
                    function = tmpFile.getName().replace(".java", ".") + function;
                    String classFile = tmpFile.getPath().replace(".java", ".class");
                    if(unwinds.get(idx) != null) {
                        commands = new String[]{"jbmc", classFile, "--function", function, "--unwind", unwinds.get(idx)};
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
                            if (filterOutput && (s.contains("**") || s.contains("FAILURE") || s.contains("VERIFICATION"))) {
                                out += s;
                            }
                            s = stdInput.readLine();
                        }
                        s = stdError.readLine();
                        while (s != null) {
                            if (filterOutput && (s.contains("**") || s.contains("FAILURE") || s.contains("VERIFICATION"))) {
                                out += s;
                            }
                            s = stdError.readLine();
                        }
                        if(!filterOutput) {
                            System.out.println(out);
                        }
                        assertFalse(out, out.contains("FAILURE") && testBehaviours.get(idx) == FunctionNameVisitor.TestBehaviour.Verifyable);
                        assertFalse(out, out.contains("SUCCESSFUL") && testBehaviours.get(idx) == FunctionNameVisitor.TestBehaviour.Fails);


                    } else {
                        System.out.println("Fucntion: " + function + " ignored due to missing annotation.");
                    }
                }
                idx++;
            }

            cleanup();
        }
    }


    @After
    public void cleanup() throws IOException {
        if(doCleanup) {
            Runtime rt = Runtime.getRuntime();
            String[] commands = new String[]{"rm", tmpFile.getPath().replace(".java", ".class")};
            Process proc;
            proc = rt.exec(commands);


            commands = new String[]{"rm", tmpFile.getPath().replace(".java", "$ReturnException.class")};
            proc = rt.exec(commands);

            commands = new String[]{"rm", "./tests/TestAnnotations/Fails.class".replaceAll("/", File.separator)};
            proc = rt.exec(commands);

            commands = new String[]{"rm", "./tests/TestAnnotations/Verifyable.class".replaceAll("/", File.separator)};
            proc = rt.exec(commands);

            commands = new String[]{"rm", "./tests/TestAnnotations/Unwind.class".replaceAll("/", File.separator)};
            proc = rt.exec(commands);

            if (!keepTmpFile) {
                commands = new String[]{"rm", tmpFile.getPath()};
                proc = rt.exec(commands);
            }
        }
    }
}

class FunctionNameVisitor extends JmlTreeScanner {
    static public List<String> functionNames = new ArrayList();
    static public List<TestBehaviour> functionBehaviours = new ArrayList<>();
    static public List<String> unwinds = new ArrayList<>();

    public enum TestBehaviour {
        Verifyable,
        Fails,
        Ignored
    }
    @Override
    public void visitJmlMethodDecl(JmlTree.JmlMethodDecl that) {
        functionNames.add(that.getName().toString());
        translateAnnotations(that.mods.annotations);
        super.visitJmlMethodDecl(that);
    }

    private void translateAnnotations(List<JCTree.JCAnnotation> annotations) {
        for(JCTree.JCAnnotation annotation : annotations) {
            if(annotation.annotationType.toString().equals("Fails")) {
                functionBehaviours.add(TestBehaviour.Fails);
            } else if(annotation.annotationType.toString().equals("Verifyable")) {
                functionBehaviours.add(TestBehaviour.Verifyable);
            } else if(annotation.annotationType.toString().equals("Unwind")) {
                try {
                    unwinds.add(((JCTree.JCAssign)annotation.args.get(0)).rhs.toString());
                } catch (Exception e) {
                    System.out.println("Cannot parse annotation " + annotation.toString());
                }
            } else {
                functionBehaviours.add(TestBehaviour.Ignored);
            }
        }
        if(functionNames.size() != functionBehaviours.size()) {
            functionBehaviours.add(TestBehaviour.Ignored);
        }
        if(functionBehaviours.size() != unwinds.size()) {
            unwinds.add(null);
        }
    }

    static void parseFile(String fileName) {
        try {
            String[] args = {fileName};
            IAPI api = Factory.makeAPI();
            java.util.List<JmlTree.JmlCompilationUnit> cu = api.parseFiles(args);
            int a = api.typecheck(cu);
            //System.out.printf("a=%d", a);

            Context ctx = api.context();
            FunctionNameVisitor fnv = new FunctionNameVisitor();
            for (JmlTree.JmlCompilationUnit it : cu) {
                //System.out.println(api.prettyPrint(rewriteRAC(it, ctx)));
                ctx.dump();
                it.accept(fnv);
            }
        } catch (Exception e) {
            System.out.println("error parsing for method names");
        }
    }
}