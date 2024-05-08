package utils;

import cli.CLI;
import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.google.common.collect.ImmutableList;
import exceptions.TranslationException;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.jupiter.params.provider.Arguments;
import translation.FunctionNameVisitor;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Created by jklamroth on 12/3/18.
 */
public class Utils {
    public static final String baseTestFolder = "." + File.separator + "testRes" + File.separator;
    private static Logger log = LogManager.getLogger(Utils.class);
    private static boolean keepTmpFile = true;
    private static boolean filterOutput = false;
    private boolean doCleanup = false;

    public static Stream<Arguments> assignableParameter() {
        return prepareParameters(baseTestFolder + "tests" + File.separator + "AssignableTests.java");
    }

    public static Stream<Arguments> assignable2Parameter() {
        return prepareParameters(baseTestFolder + "tests" + File.separator + "AssignableTests2.java");
    }

    public static Stream<Arguments> prepareParameters(String fileName) {
        ArrayList<Arguments> params = new ArrayList<>();
        createAnnotationsFolderOld(fileName);
        CLI.keepTranslation = keepTmpFile;
        CLI.debugMode = true;
        File tmpFile = CLI.prepareForJBMC(fileName);
        if (tmpFile == null) {
            log.error("Someting went wrong. Test aborted.");
            throw new TranslationException("Tmpfile was not created. abort test.");
        }
        String classFile = "tests" + File.separator + tmpFile.getName().replace(".java", "");

        log.debug("Parsing file for functions.");
        ParserConfiguration config = new ParserConfiguration();
        config.setJmlKeys(ImmutableList.of(ImmutableList.of("openjml")));
        config.setProcessJml(true);
        //TODO this should be checked if this is fine
        config.setSymbolResolver(new JavaSymbolSolver(new JavaParserTypeSolver(new File(fileName).toPath().getParent())));
        JavaParser parser = new JavaParser(config);

        List<CompilationUnit> compilationUnits = new ArrayList<>(32);
        ParseResult<CompilationUnit> result = parser.parse(fileName);
        if (result.isSuccessful()) {
            compilationUnits.add(result.getResult().get());
        } else {
            System.out.println(fileName);
            result.getProblems().forEach(System.out::println);
        }
        assert compilationUnits.size() == 1;
        List<TestOptionsListener.TestOptions> testOptions = new ArrayList<>();
        compilationUnits.get(0).accept(new TestOptionsListener(), testOptions);

        for (TestOptionsListener.TestOptions to : testOptions) {
            if (to.behaviour != TestBehaviour.Ignored) {
                String name = to.functionName;
                if (!name.contains("<init>")) {
                    int dotIdx = name.lastIndexOf(":");
                    name = name.substring(0, dotIdx) + "Verf" + name.substring(dotIdx);
                }
                params.add(Arguments.of(classFile, name, to.unwinds, to.behaviour, tmpFile.getParentFile().getParent()));
            }
        }
        log.debug("Found " + params.size() + " functions.");
        return params.stream();
    }

    private static void createAnnotationsFolderOld(String fileName) {
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
            System.out.println(e.getMessage());
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

    private static void createAnnotationsFolder(String fileName) {
        var f = Paths.get(fileName);
        var dir = f.getParent().resolveSibling("tmp/testannotations");
        log.debug("Copying Annotation files to " + dir.toAbsolutePath());
        try {
            Files.createDirectories(dir);
            Files.copy(Paths.get("./tests/testannotations/Fails.java"),
                    dir.resolveSibling("Fails.java"),
                    StandardCopyOption.REPLACE_EXISTING);

            Files.copy(Paths.get("./tests/testannotations/Verifyable.java"),
                    dir.resolveSibling("Verifyable.java"),
                    StandardCopyOption.REPLACE_EXISTING);

            Files.copy(Paths.get("./tests/testannotations/Unwind.java"),
                    dir.resolveSibling("Unwind.java"),
                    StandardCopyOption.REPLACE_EXISTING);

        } catch (IOException e) {
            e.printStackTrace();
            System.out.println(e.getMessage());
            throw new TranslationException("Error trying to copy TestAnnotations");
        }
    }

    public static void runTests(String classFile, String function, String unwind, TestBehaviour behaviour, String parentFolder)
            throws IOException, InterruptedException {
        if (behaviour != TestBehaviour.Ignored) {
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
            File parentDir = new File("." + File.separator + "testRes" + File.separator + "tests" + File.separator + "tmp");
            if (!Files.exists(new File(parentDir, classFile + ".class").toPath())) {
                System.out.println("Classfile not found: " + new File(parentDir, classFile + ".class").toPath());
            }
            System.out.println(parentDir);
            Process proc = rt.exec(commands, null, parentDir);


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
            assertFalse(out.toString().contains("FAILURE") && behaviour == TestBehaviour.Verifiable);
            assertFalse(out.toString().contains("SUCCESSFUL") && behaviour == TestBehaviour.Failing);
            assertTrue(out.toString().contains("VERIFICATION"));

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

