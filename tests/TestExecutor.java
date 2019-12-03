import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.Factory;
import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.*;
import java.nio.file.CopyOption;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Created by jklamroth on 12/3/18.
 */
public class TestExecutor {
    private static final String baseTestFolder = "testRes" + File.separator;
    static String[] fileNames = {baseTestFolder + "tests/TestSuite.java", baseTestFolder + "tests/AssignableTests.java", baseTestFolder + "tests/AssignableTests2.java"};
    private File tmpFile = new File(baseTestFolder + "tmp.java");
    private boolean keepTmpFile = true;
    private boolean filterOutput = true;
    private boolean doCleanup = false;

    @Before
    public void init() {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
    }

    @org.junit.Test
    public void runBubbleSortSymbCaseStudy() throws IOException, InterruptedException {
        fileNames = new String[]{baseTestFolder + "CaseStudy/BubbleSortSymb.java"};
        runAllTests();
    }

    @org.junit.Test
    public void runOpenJMLDemos() throws IOException, InterruptedException {
        File folder = new File("./testRes/openJMLDemo");
        File[] files = folder.listFiles(File::isFile);
        String[] fileNames = new String[files.length];
        for(int i = 0; i < files.length; ++i) {
            if(files[i].isFile()) {
                fileNames[i] = files[i].getPath();
            }
        }
        runCaseStudies(fileNames);
    }

    @org.junit.Test
    public void runOpenJMLDemo() throws IOException, InterruptedException {
        String[] fileNames = new String[]{"./testRes/openJMLDemo/Taxpayer.java"};
        runCaseStudies(fileNames);
    }

    @org.junit.Test
    public void runPairInsertionSortCaseStudy() throws IOException, InterruptedException {
        runTests(new String[]{baseTestFolder + "CaseStudy/PairInsertionSort.java"});
    }

    @org.junit.Test
    public void runPairInsertionSortSymbCaseStudy() throws IOException, InterruptedException {
        runTests(new String[]{baseTestFolder + "CaseStudy/PairInsertionSortSymb.java"});
    }

    @org.junit.Test
    public void runMultCaseStudy() throws IOException, InterruptedException {
        runTests(new String[]{baseTestFolder + "CaseStudy/MultExample.java"});
    }

    @org.junit.Test
    public void runBitMagicCaseStudy() throws IOException, InterruptedException {
        runTests(new String[]{baseTestFolder + "CaseStudy/BitMagicCollection.java"});
    }

    @org.junit.Test
    public void runDualPivotQSCaseStudy() throws IOException, InterruptedException {
        runTests(new String[]{baseTestFolder + "CaseStudy/DualPivotQuicksort.java"});
    }

    @org.junit.Test
    public void runBubbleSortCaseStudy() throws IOException, InterruptedException {
        runTests(new String[]{baseTestFolder + "CaseStudy/BubbleSort.java"});
    }

    @org.junit.Test
    public void runHammingWeightCaseStudy() throws IOException, InterruptedException {
        runTests(new String[]{baseTestFolder + "CaseStudy/HammingWeight.java"});
    }

    @org.junit.Test
    public void runBigIntCaseStudy() throws IOException, InterruptedException {
        runTests(new String[]{baseTestFolder + "CaseStudy/BigInt.java"});
    }

    @org.junit.Test
    public void runTmpTest() throws IOException, InterruptedException {
        runTests(new String[]{baseTestFolder + "CaseStudy/TmpTest.java"});
    }

    @org.junit.Test
    public void runSomeTest() throws IOException, InterruptedException {
        runTests(new String[]{baseTestFolder + "RemoveDup.java"});
    }

    @org.junit.Test
    public void runFailingTests() throws IOException, InterruptedException {
        runTests(new String[]{baseTestFolder + "FailingTests.java"});
    }

    @org.junit.Test
    public void runAssignableTests() throws IOException, InterruptedException {
        runTests(new String[]{baseTestFolder + "tests/AssignableTests.java", baseTestFolder + "tests/AssignableTests2.java"});
    }

    static private void createAnnotationsFolder(String fileName) {
        File f = new File(fileName);
        File dir = new File(f.getParent(),"tmp" + File.separator + "TestAnnotations" );
        System.out.println("Copying Annotation files to " + dir.getAbsolutePath());
        dir.mkdirs();
        try {
            Files.copy(new File("./tests/TestAnnotations/Fails.java").toPath(), new File(dir,"Fails.java").toPath(), StandardCopyOption.REPLACE_EXISTING);
            Files.copy(new File("./tests/TestAnnotations/Verifyable.java").toPath(), new File(dir,"Verifyable.java").toPath(), StandardCopyOption.REPLACE_EXISTING);
            Files.copy(new File("./tests/TestAnnotations/Unwind.java").toPath(), new File(dir,"Unwind.java").toPath(), StandardCopyOption.REPLACE_EXISTING);
        } catch (IOException e) {
            e.printStackTrace();
            throw new RuntimeException("Error trying to copy TestAnnotations");
        }
    }

    public void runCaseStudies(String[] files) throws IOException, InterruptedException {
        for(String fileName : files) {
            System.out.println("Running tests for file: " + fileName);
            createAnnotationsFolder(fileName);
            CLI.keepTranslation = keepTmpFile;
            File tmpFile = CLI.prepareForJBMC(fileName);
            if(tmpFile == null) {
                System.out.println("Someting went wrong. Test aborted.");
                return;
            }
            FunctionNameVisitor.parseFile(tmpFile.getPath());

            List<String> functionNames = FunctionNameVisitor.functionNames;
            for(String function : functionNames) {
                if(function.endsWith("Symb") || function.endsWith("<init>")) {
                    continue;
                }
                System.out.println("Running test for function: " + function);
                //commands = new String[] {"jbmc", tmpFile.getAbsolutePath().replace(".java", ".class")};
                String classFile = tmpFile.getPath().replace(".java", ".class");
                String[] commands = null;

                commands = new String[]{new File(tmpFile.getParent(), "jbmc").getAbsolutePath(), classFile, "--function", function, "--trace", "--unwind", "7"};

                Runtime rt = Runtime.getRuntime();
                Process proc = rt.exec(commands);
                proc.waitFor();

                BufferedReader stdInput = new BufferedReader(new
                        InputStreamReader(proc.getInputStream()));

                BufferedReader stdError = new BufferedReader(new
                        InputStreamReader(proc.getErrorStream()));

                String s = stdInput.readLine();
                String out = "";
                if (s != null) {
                    out += "JBMC Output for file: " + tmpFile.getPath().replace(".java", ".class") + " with function " + function + "\n";
                    while (s != null) {
                        if (!filterOutput || (s.contains("**") || s.contains("FAILURE") || s.contains("VERIFICATION"))) {
                            out += s +"\n";
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
                    if(!filterOutput) {
                        System.out.println(out);
                    }
                    assertTrue(out, out.contains("SUCCESSFUL"));
                    assertTrue(out, out.contains("VERIFICATION"));
                } else {
                    System.out.println("Function: " + function + " ignored due to missing annotation.");
                }
            }
            //CLI.cleanUp();
        }
    }

    public void runTests(String[] files) throws IOException, InterruptedException {
        for(String fileName : files) {
            createAnnotationsFolder(fileName);
            CLI.keepTranslation = keepTmpFile;
            File tmpFile = CLI.prepareForJBMC(fileName);
            if(tmpFile == null) {
                System.out.println("Someting went wrong. Test aborted.");
                return;
            }
            FunctionNameVisitor.parseFile(tmpFile.getPath());
            List<FunctionNameVisitor.TestBehaviour> testBehaviours = FunctionNameVisitor.functionBehaviours;
            List<String> functionNames = FunctionNameVisitor.functionNames;
            List<String> unwinds = FunctionNameVisitor.unwinds;
            assertEquals(functionNames.size(), testBehaviours.size());
            assertEquals(functionNames.size(), unwinds.size());
            int idx = 0;
            System.out.println("Running " +
                    testBehaviours.stream().
                            filter(b -> b != FunctionNameVisitor.TestBehaviour.Ignored).
                            collect(Collectors.toList()).size() +
                    " tests in file: " + tmpFile.getName());
            for(String function : functionNames) {
                if(testBehaviours.get(idx) != FunctionNameVisitor.TestBehaviour.Ignored) {
                    System.out.println("Running test for function: " + function);
                    //commands = new String[] {"jbmc", tmpFile.getAbsolutePath().replace(".java", ".class")};
                    String classFile = tmpFile.getPath().replace(".java", ".class");
                    String[] commands;
                    if(unwinds.get(idx) != null) {
                        commands = new String[]{new File(tmpFile.getParent(), "jbmc").getAbsolutePath(), classFile, "--function", function, "--unwind", unwinds.get(idx), "--unwinding-assertions", "--trace"};
                    } else {
                        commands = new String[]{new File(tmpFile.getParent(), "jbmc").getAbsolutePath(), classFile, "--function", function};
                    }

                    Runtime rt = Runtime.getRuntime();
                    Process proc = rt.exec(commands);
                    proc.waitFor();

                    BufferedReader stdInput = new BufferedReader(new
                            InputStreamReader(proc.getInputStream()));

                    BufferedReader stdError = new BufferedReader(new
                            InputStreamReader(proc.getErrorStream()));

                    String s = stdInput.readLine();
                    String out = "";
                    if (s != null) {
                        out += "JBMC Output for file: " + tmpFile.getPath().replace(".java", ".class") + " with function " + function + "\n";
                        while (s != null) {
                            if (!filterOutput || (s.contains("**") || s.contains("FAILURE") || s.contains("VERIFICATION"))) {
                                out += s +"\n";
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
                        if(!filterOutput) {
                            System.out.println(out);
                        }
                        assertFalse(out, out.contains("FAILURE") && testBehaviours.get(idx) == FunctionNameVisitor.TestBehaviour.Verifyable);
                        assertFalse(out, out.contains("SUCCESSFUL") && testBehaviours.get(idx) == FunctionNameVisitor.TestBehaviour.Fails);
                        assertTrue(out, out.contains("VERIFICATION"));


                    } else {
                        System.out.println("Function: " + function + " ignored due to missing annotation.");
                    }
                }
                idx++;
            }
            CLI.cleanUp();
        }
    }

    @org.junit.Test
    public void runAllTests() throws IOException, InterruptedException {
        runTests(fileNames);
    }

    @Test
    public void test() {
        int[] arr = new int[5];
        Arrays.stream(arr).forEach(i -> System.out.println("i = " + i));
    }


    @After
    public void cleanup() {
        if(!keepTmpFile) {
            CLI.cleanUp();
        }
    }
}

class FunctionNameVisitor extends JmlTreeScanner {
    static private String packageName = "";
    static public List<String> functionNames = new ArrayList();
    static public List<TestBehaviour> functionBehaviours = new ArrayList<>();
    static public List<String> unwinds = new ArrayList<>();
    static private String className = "";

    public enum TestBehaviour {
        Verifyable,
        Fails,
        Ignored
    }

    @Override
    public void visitJmlClassDecl(JmlTree.JmlClassDecl that) {
        className = that.getSimpleName().toString();
        super.visitJmlClassDecl(that);
    }

    @Override
    public void visitJmlMethodDecl(JmlTree.JmlMethodDecl that) {
        String f;
        if(!packageName.equals("")) {
            f = packageName + "." + className + "." + that.getName().toString();
        } else {
            f = className + "." + that.getName().toString();
        }
        String rtString = returnTypeString(that.restype);
        String paramString = getParamString(that.params);
        functionNames.add(f + ":" + paramString + rtString);
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
        functionNames = new ArrayList();
        functionBehaviours = new ArrayList<>();
        unwinds = new ArrayList<>();
        try {
            String[] args = {fileName};
            IAPI api = Factory.makeAPI();
            java.util.List<JmlTree.JmlCompilationUnit> cu = api.parseFiles(args);
            int a = api.typecheck(cu);
            //System.out.printf("a=%d", a);

            Context ctx = api.context();
            FunctionNameVisitor fnv = new FunctionNameVisitor();
            for (JmlTree.JmlCompilationUnit it : cu) {
                if(it.pid != null) {
                    packageName = it.pid.toString();
                }
                //System.out.println(api.prettyPrint(rewriteRAC(it, ctx)));
                ctx.dump();
                it.accept(fnv);
            }
        } catch (Exception e) {
            System.out.println("error parsing for method names");
        }
    }

    private String returnTypeString(JCTree.JCExpression rtType) {
        return typeToString(rtType);
    }

    private String getParamString(List<JCTree.JCVariableDecl> params) {
        String res = "(";
        for(JCTree.JCVariableDecl p : params) {
            res += typeToString(p.vartype);
        }
        return res + ")";
    }

    private String typeToString(JCTree.JCExpression type) {
        if(type instanceof JCTree.JCPrimitiveTypeTree) {
            if(type.toString().equals("void"))
                return "V";
            if(type.toString().equals("int"))
                return "I";
            if(type.toString().equals("float"))
                return "F";
            if(type.toString().equals("double"))
                return "D";
            if(type.toString().equals("char"))
                return "C";
            if(type.toString().equals("long"))
                return "J";
            if(type.toString().equals("boolean"))
                return "Z";
            throw new RuntimeException("Unkown type " + type.toString() + ". Cannot call JBMC.");
        } else if(type instanceof JCTree.JCArrayTypeTree) {
            return "[" + typeToString(((JCTree.JCArrayTypeTree) type).elemtype);
        } else if (type != null) {
            return "L" + ((JCTree.JCIdent)type).sym.toString().replace(".", "/") + ";";
        }
        return "V";
    }
}
