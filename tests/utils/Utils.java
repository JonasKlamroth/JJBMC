package utils;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import cli.CLI;
import exceptions.TranslationException;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import translation.FunctionNameVisitor;


/**
 * Created by jklamroth on 12/3/18.
 */
public class Utils {
    public static final String baseTestFolder = "testRes" + File.separator;
    private static Logger log = LogManager.getLogger(Utils.class);
    private static boolean keepTmpFile = true;
    private static boolean filterOutput = false;
    private boolean doCleanup = false;

    public static Collection<Object[]> assignableParameter() {
        return prepareParameters(baseTestFolder + "tests" + File.separator + "AssignableTests.java");
    }

    public static Collection<Object[]> assignable2Parameter() {
        return prepareParameters(baseTestFolder + "tests" + File.separator + "AssignableTests2.java");
    }

    public static Collection<Object[]> prepareParameters(String fileName) {
        ArrayList<Object[]> params = new ArrayList<>();
        createAnnotationsFolder(fileName);
        CLI.keepTranslation = keepTmpFile;
        CLI.debugMode = true;
        File tmpFile = CLI.prepareForJBMC(fileName);
        if (tmpFile == null) {
            log.error("Someting went wrong. Test aborted.");
            throw new TranslationException("Tmpfile was not created. abort test.");
        }
        String classFile = "tests" + File.separator + tmpFile.getName().replace(".java", "");

        log.debug("Parsing file for functions.");
        FunctionNameVisitor.parseFile(fileName, true);
        List<FunctionNameVisitor.TestBehaviour> testBehaviours = FunctionNameVisitor.getFunctionBehaviours();
        List<String> functionNames = FunctionNameVisitor.getFunctionNames();
        List<String> unwinds = FunctionNameVisitor.getUnwinds();
        assert (functionNames.size() == testBehaviours.size());
        assert (functionNames.size() == unwinds.size());

        for (int idx = 0; idx < functionNames.size(); ++idx) {
            if (testBehaviours.get(idx) != FunctionNameVisitor.TestBehaviour.Ignored) {
                String name = functionNames.get(idx);
                if (!name.contains("<init>")) {
                    int dotIdx = name.lastIndexOf(":");
                    name = name.substring(0, dotIdx) + "Verf" + name.substring(dotIdx);
                }
                params.add(new Object[] {classFile, name, unwinds.get(idx), testBehaviours.get(idx), tmpFile.getParentFile().getParent()});
            }
        }
        log.debug("Found " + params.size() + " functions.");
        return params;
    }

    private static void createAnnotationsFolder(String fileName) {
        File f = new File(fileName);
        File dir = new File(f.getParent(), "tmp" + File.separator + "testannotations");
        log.debug("Copying Annotation files to " + dir.getAbsolutePath());
        dir.mkdirs();
        try {
            Files.copy(new File("." + File.separator + "tests" + File.separator + "testannotations" + File.separator + "Fails.java").toPath(),
                new File(dir, "Fails.java").toPath(), StandardCopyOption.REPLACE_EXISTING);
            Files.copy(new File("." + File.separator + "tests" + File.separator + "testannotations" + File.separator + "Verifyable.java").toPath(),
                new File(dir, "Verifyable.java").toPath(), StandardCopyOption.REPLACE_EXISTING);
            Files.copy(new File("." + File.separator + "tests" + File.separator + "testannotations" + File.separator + "Unwind.java").toPath(),
                new File(dir, "Unwind.java").toPath(), StandardCopyOption.REPLACE_EXISTING);
        } catch (IOException e) {
            e.printStackTrace();
            throw new TranslationException("Error trying to copy TestAnnotations");
        }
        f = new File(fileName);
        dir = new File(f.getParent(), "tmp" + File.separator + "tests" + File.separator + "testannotations");
        log.debug("Copying Annotation files to " + dir.getAbsolutePath());
        dir.mkdirs();
        try {
            Files.copy(new File("." + File.separator + "tests" + File.separator + "testannotations" + File.separator + "Fails.java").toPath(),
                new File(dir, "Fails.java").toPath(), StandardCopyOption.REPLACE_EXISTING);
            Files.copy(new File("." + File.separator + "tests" + File.separator + "testannotations" + File.separator + "Verifyable.java").toPath(),
                new File(dir, "Verifyable.java").toPath(), StandardCopyOption.REPLACE_EXISTING);
            Files.copy(new File("." + File.separator + "tests" + File.separator + "testannotations" + File.separator + "Unwind.java").toPath(),
                new File(dir, "Unwind.java").toPath(), StandardCopyOption.REPLACE_EXISTING);
        } catch (IOException e) {
            e.printStackTrace();
            throw new TranslationException("Error trying to copy TestAnnotations");
        }
    }

    public static void runTests(String classFile, String function, String unwind, FunctionNameVisitor.TestBehaviour behaviour, String parentFolder)
        throws IOException, InterruptedException {
        if (behaviour != FunctionNameVisitor.TestBehaviour.Ignored) {
            log.info("Running test for function: " + function);
            //commands = new String[] {"jbmc", tmpFile.getAbsolutePath().replace(".java", ".class")};

            List<String> commandList = new ArrayList<>();
            if (System.getProperty("os.name").toLowerCase().startsWith("windows")) {
                if (function.contains("()")) {
                    function = function.replace("<init>", "<clinit>");
                }
                function = "\"" + function + "\"";
                classFile = classFile.replaceAll("\\\\", "/");
                commandList.add("cmd.exe");
                commandList.add("/c");
            }

            commandList.add("jbmc");
            commandList.add(classFile);
            commandList.add("--function");
            commandList.add(function);

            if (unwind != null) {
                commandList.add("--unwind");
                commandList.add(unwind);
            }

            String[] commands = new String[commandList.size()];
            commands = commandList.toArray(commands);

            log.info("Run jbmc with commands: " + Arrays.toString(commands));

            Runtime rt = Runtime.getRuntime();
            Process proc = rt.exec(commands, null, new File("." + File.separator + "testRes" + File.separator + "tests" + File.separator + "tmp"));


            BufferedReader stdInput = new BufferedReader(new
                    InputStreamReader(proc.getInputStream()));

            BufferedReader stdError = new BufferedReader(new
                    InputStreamReader(proc.getErrorStream()));

            String s = stdInput.readLine();
            String error = stdError.readLine();
            StringBuilder out = new StringBuilder();
            StringBuilder errOut = new StringBuilder();
            out.append("JBMC Output for file: ").append(classFile).append(" with function ").append(function).append("\n");
            while (s != null) {
                if (!filterOutput || (s.contains("**") || s.contains("FAILURE") || s.contains("VERIFICATION"))) {
                    out.append(s).append("\n");
                }
                s = stdInput.readLine();
            }
            while (error != null) {
                errOut.append(error).append("\n");
                error = stdError.readLine();
            }

            proc.waitFor();
            if (!filterOutput) {
                log.info(out);
                log.info(errOut);
            }
            assertFalse(out.toString(), out.toString().contains("FAILURE") && behaviour == FunctionNameVisitor.TestBehaviour.Verifyable);
            assertFalse(out.toString(), out.toString().contains("SUCCESSFUL") && behaviour == FunctionNameVisitor.TestBehaviour.Fails);
            assertTrue(out.toString(), out.toString().contains("VERIFICATION"));

        } else {
            log.warn("Function: " + function + " ignored due to missing annotation.");
        }
    }

    public void runCaseStudies(String[] files) {
        for (String fileName : files) {
            CLI.translateAndRunJBMC(fileName);
        }
    }

    //@org.junit.Test
    //public void runAllTests() throws IOException, InterruptedException {
    //    runTests(fileNames);
    //}

    public void cleanup() {
        if (!keepTmpFile) {
            CLI.cleanUp();
        }
    }
}

