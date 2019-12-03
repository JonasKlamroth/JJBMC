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
import java.util.stream.DoubleStream;

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

    @org.junit.Test
    public void runAWSTests() throws IOException, InterruptedException {
        runCaseStudies(new String[]{baseTestFolder + "AWS/CipherBlockHeaders.java"});
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
            CLI.keepTranslation = keepTmpFile;
            File tmpFile = CLI.prepareForJBMC(fileName);
            if(tmpFile == null) {
                System.out.println("Someting went wrong. Test aborted.");
                return;
            }
            FunctionNameVisitor.parseFile(tmpFile.getPath());

            List<String> functionNames = FunctionNameVisitor.getFunctionNames();
            for(String function : functionNames) {
                if(function.contains("Symb")) {
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
                    if (out.contains("SUCCESSFUL")) {
                        System.out.println("Sucessfull");
                    } else {
                        System.out.println("Fail:");
                        System.out.println(out);
                    }
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
            List<FunctionNameVisitor.TestBehaviour> testBehaviours = FunctionNameVisitor.getFunctionBehaviours();
            List<String> functionNames = FunctionNameVisitor.getFunctionNames();
            List<String> unwinds = FunctionNameVisitor.getUnwinds();
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

