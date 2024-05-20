package jjbmc.utils;

import jjbmc.JJBMCOptions;
import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.google.common.collect.ImmutableList;
import jjbmc.ErrorLogger;
import jjbmc.Operations;
import jjbmc.FunctionNameVisitor.TestBehaviour;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;
import java.util.stream.Stream;

import static jjbmc.ErrorLogger.*;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Created by jklamroth on 12/3/18.
 */
public class Utils {
    public static final Path SRC_TEST_JAVA = Paths.get("src", "test", "java");

    public static final Path TMP_FOLDER = Paths.get("tmp");

    private static final ErrorLogger log = new ErrorLogger();
    private static final boolean filterOutput = false;

    public static Stream<JJBMCTest> prepareParameters(Path fileName) throws Exception {
        createAnnotationsFolder(fileName);

        //CLI.keepTranslation = keepTmpFile;
        //CLI.debugMode = true;
        JJBMCOptions options = new JJBMCOptions();
        options.keepTranslation = true;
        options.setDebugMode(true);
        options.setFileName(fileName);

        Operations operations = new Operations(options);
        var tmpFile = operations.prepareForJBMC(fileName);

        var classFile = Paths.get("tests",
                tmpFile.getFileName().toString().replace(".java", ""));

        debug("Parsing file for functions.");
        ParserConfiguration config = new ParserConfiguration();
        config.setJmlKeys(ImmutableList.of(ImmutableList.of("openjml")));
        config.setProcessJml(true);
        //TODO this should be checked if this is fine
        config.setSymbolResolver(new JavaSymbolSolver(new JavaParserTypeSolver(fileName.getParent())));
        JavaParser parser = new JavaParser(config);

        List<CompilationUnit> compilationUnits = new ArrayList<>(32);
        ParseResult<CompilationUnit> result;
        try {
            result = parser.parse(fileName);
        } catch (IOException e) {
            System.out.println("Error parsing file: " + fileName);
            throw new RuntimeException(e);
        }
        if (result.isSuccessful()) {
            compilationUnits.add(result.getResult().get());
        } else {
            System.out.println(fileName);
            result.getProblems().forEach(System.out::println);
        }
        assert compilationUnits.size() == 1;
        List<TestOptions> testOptions = new ArrayList<>();
        compilationUnits.get(0).accept(new TestOptionsListener(), testOptions);

        var params = testOptions.stream()
                .filter(it -> it.behaviour() != TestBehaviour.Ignored)
                .map(it -> new JJBMCTest(operations, it));
        debug("Found %s functions", testOptions.size());
        return params;
    }


    private static void createAnnotationsFolder(Path path) throws IOException {
        var dir = path.getParent().resolve("tmp/testannotations");
        info("Copying Annotation files to {}", dir.toAbsolutePath());

        Files.createDirectories(dir);

        Files.copy(SRC_TEST_JAVA.resolve("testannotations/Fails.java"),
                dir.resolve("Fails.java"),
                StandardCopyOption.REPLACE_EXISTING);

        Files.copy(SRC_TEST_JAVA.resolve("testannotations/Verifyable.java"),
                dir.resolve("Verifyable.java"),
                StandardCopyOption.REPLACE_EXISTING);

        Files.copy(SRC_TEST_JAVA.resolve("testannotations/Unwind.java"),
                dir.resolve("Unwind.java"),
                StandardCopyOption.REPLACE_EXISTING);
    }

    public static void runTests(JJBMCTest test) throws InterruptedException, IOException {
        var topts = test.topts();
        var opts = test.op().getOptions();

        var function = topts.functionName();
        var classFile = Objects.requireNonNull(opts.getTmpFile());
        var unwind = topts.unwinds();

        if (topts.behaviour() == TestBehaviour.Ignored) {
            warn("Function: %s ignored due to missing annotation.", function);
            return;
        }

        info("Running test for function: %s", function);

        List<String> commandList = new ArrayList<>();
        if (opts.isWindows()) {
            if (function.contains("()")) {
                function = function.replace("<init>", "<clinit>");
            }
            function = "\"%s\"".formatted(function);
            //classFile = classFile.replaceAll("\\\\", "/");
            commandList.add("cmd.exe");
            commandList.add("/c");
        }

        commandList.add("jbmc");
        commandList.add(classFile.toAbsolutePath().toString());
        commandList.add("--function");
        commandList.add(function);

        if (unwind != -1) {
            commandList.add("--unwind");
            commandList.add(String.valueOf(unwind));
        }

        String[] commands = new String[commandList.size()];
        commands = commandList.toArray(commands);

        info("Run jbmc with commands: " + Arrays.toString(commands));

        Runtime rt = Runtime.getRuntime();
        File parentDir = new File("." + File.separator + "testRes" + File.separator + "tests" + File.separator + "tmp");
        if (!Files.exists(new File(parentDir, classFile + ".class").toPath())) {
            System.out.println("Classfile not found: " + new File(parentDir, classFile + ".class").toPath());
        }
        System.out.println(parentDir);
        Process proc = new ProcessBuilder(commandList).directory(parentDir).start();


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
            info(out);
            info(errOut);
        }
        TestBehaviour behaviour = topts.behaviour();

        assertFalse(out.toString().contains("FAILURE") && behaviour == TestBehaviour.Verifyable);
        assertFalse(out.toString().contains("SUCCESSFUL") && behaviour == TestBehaviour.Fails);
        assertTrue(out.toString().contains("VERIFICATION"));

    }
}
