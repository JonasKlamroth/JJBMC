package jjbmc;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.TypeSolverBuilder;
import com.google.common.collect.ImmutableList;
import jjbmc.jml2java.Jml2JavaFacade;
import jjbmc.trace.TraceParser;
import lombok.Getter;
import lombok.RequiredArgsConstructor;
import org.jspecify.annotations.Nullable;

import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.ToolProvider;
import java.io.*;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.util.*;
import java.util.concurrent.*;

import static jjbmc.ErrorLogger.*;

@RequiredArgsConstructor
@Getter
public class Operations implements Callable<Integer> {
    private final JJBMCOptions options;
    @Nullable
    private Process jbmcProcess;
    private List<String> jbmcOptions = new LinkedList<>();

    public static CompilationUnit translate(File file, JJBMCOptions options) throws Exception {
        return translate(options, file.toPath());
    }

    @Getter
    private boolean didCleanUp = false;

    public static CompilationUnit translate(JJBMCOptions options, Path fileName) throws Exception {
        ParserConfiguration config = new ParserConfiguration();
        config.setJmlKeys(ImmutableList.of(ImmutableList.of("openjml")));
        config.setProcessJml(true);
        config.setSymbolResolver(new JavaSymbolSolver(
                new TypeSolverBuilder()
                        .withSourceCode(options.getTmpFolder())
                        .withCurrentJRE()
                        .build()));
        JavaParser parser = new JavaParser(config);

        List<CompilationUnit> compilationUnits = new ArrayList<>(32);
        ParseResult<CompilationUnit> result = parser.parse(fileName);
        if (result.isSuccessful()) {
            var compilationUnit = result.getResult().get();
            return rewriteAssert(compilationUnit, options);
        } else {
            result.getProblems().forEach(System.out::println);
            final var first = result.getProblems().get(0);
            throw new RuntimeException(first.getVerboseMessage(), first.getCause().orElse(null));
        }
    }

    private static void copySubjectOfVerification(Path fileName, Path tmpFile) throws IOException {
        Files.copy(fileName, tmpFile, StandardCopyOption.REPLACE_EXISTING);
    }

    private static void createCProverFolder(Path folder) throws IOException {
        var dir = folder.resolve("org/cprover");
        debug("Copying CProver.java to %s", dir.toAbsolutePath());
        Files.createDirectories(dir);
        try (InputStream is = JJBMCOptions.class.getResourceAsStream("/cli/CProver.java")) {
            Files.copy(Objects.requireNonNull(is), dir.resolve("CProver.java"));
        }
    }

    public void translateAndRunJBMC(Path file, String functionName) throws Exception {
        options.functionName = functionName;
        options.setFileName(file);
        translateAndRunJBMC();
    }

    public void prepareSource() throws Exception {
        didCleanUp = false;

        if (options.getMaxArraySize() > options.getUnwinds() - 2) {
            warn("Unwinds is set to less than maxArraySize + 2. This may lead to unsound behaviour.");
        }


        final var file = options.getFileName();
        if (!Files.exists(file)) {
            throw new FileNotFoundException("Could not find file " + file);
        }

        var tmpFile = options.getTmpFile();

        try {
            deleteFolder(options.getTmpFolder(), true);
            Files.createDirectories(options.getTmpFolder());

            /*var tmpClassFile = options.getTmpFolder().resolve(
                    file.getFileName().toString()
                            .replace(".java", ".class"));

            Files.deleteIfExists(tmpFile);
            Files.deleteIfExists(tmpClassFile);
             */

            copyLibraryFiles(options.getTmpFolder());
            createCProverFolder(options.getTmpFolder());
            copySubjectOfVerification(file, tmpFile);

            long start = System.currentTimeMillis();
            var translation = translate(options, tmpFile);
            long finish = System.currentTimeMillis();
            debug("Translation.Translation took: " + (finish - start) + "ms");

            String packageName = translation.getPackageDeclaration()
                    .map(NodeWithName::getNameAsString).orElse("");
            Files.deleteIfExists(tmpFile);
            packageName = packageName.replace(".", "/");
            var packageFolder = options.getTmpFolder().resolve(packageName);
            Files.createDirectories(packageFolder);
            options.setTmpFile(packageFolder.resolve(tmpFile.getFileName()));
            var content = Jml2JavaFacade.pprint(translation);
            Files.writeString(options.getTmpFile(), content, StandardOpenOption.CREATE);
        } finally {
            options.keepTranslation = true;
            cleanUp();
        }
    }

    public void compile() throws Exception {
        if (!compileWithApi()) {
            compileWithJavac();
        }
    }

    private boolean compileWithApi() throws IOException {
        var javac = ToolProvider.getSystemJavaCompiler();
        if (javac == null) return false;

        DiagnosticCollector<JavaFileObject> diagnostics = new DiagnosticCollector<>();
        var fileManager = javac.getStandardFileManager(diagnostics, Locale.ENGLISH, Charset.defaultCharset());

        //StringWriter output = new StringWriter();
        //List<String> classes = new ArrayList<>();
        try (var s = Files.walk(options.getTmpFolder())) {
            var files = s.filter(f -> !Files.isDirectory(f))
                    .filter(f -> f.getFileName().toString().endsWith(".java"))
                    .toList();

            Iterable<? extends JavaFileObject> compilationUnits =
                    fileManager.getJavaFileObjects(files.toArray(new Path[0]));

            JavaCompiler.CompilationTask task = javac.getTask(new PrintWriter(System.out),
                    fileManager, diagnostics, List.of("-g"), List.of(), compilationUnits);

            long start = System.currentTimeMillis();
            var b = task.call();
            long stop = System.currentTimeMillis();

            info("Compilation took %d ms using the internal API", stop - start);

            for (var diagnostic : diagnostics.getDiagnostics()) {
                info("%s", diagnostic);
            }
        }
        return true;
    }

    private void compileWithJavac() throws Exception {
        var tmpFile = options.getTmpFile();
        var commands = new ArrayList<>(List.of(options.getJavacBinary().toString(), "-g",
                options.getTmpFolder().relativize(tmpFile).toString()));
        commands.addAll(options.apiArgs);

        debug("Compiling translated file: " + commands);
        var out = ProcessBuilder.Redirect.to(options.getTmpFolder().resolve("compilationErrors.txt").toFile());
        ProcessBuilder pb = new ProcessBuilder(commands)
                .redirectOutput(out)
                .redirectError(out)
                .directory(options.getTmpFolder().toFile());

        Process proc = pb.start();
        proc.waitFor();
        if (proc.exitValue() != 0) {
            options.keepTranslation = true;
            throw new Exception("Compilation failed. See compilationErrors.txt for javac output.");
        }

        debug("Compilation successful.");

        if (!JbmcFacade.verifyJBMCVersion(options.jbmcBin, options.isWindows())) {
            throw new Exception("Unverified JBMC version");
        }
    }

    private void copyLibraryFiles(Path fileName) throws IOException {
        for (String s : options.libFiles) {
            var tmpF = fileName.resolveSibling(s);
            if (!Files.exists(tmpF)) {
                throw new FileNotFoundException("Could not find libFile: " + tmpF);
            } else {
                copySubjectOfVerification(tmpF, options.getTmpFolder().resolve(tmpF.getFileName()));
            }
        }
    }

    private static List<String> prepareJBMCOptions(List<String> options) {
        List<String> res = new ArrayList<>();
        for (String s : options) {
            res.addAll(Arrays.asList(s.split(" ")));
        }
        return res;
    }

    public void translateAndRunJBMC() throws Exception {
        prepareSource();
        compile();

        var fnv = FunctionNameVisitor.parseFile(options.getTmpFile(), true);
        var functionNames = fnv.getFunctionNames();
        var paramMap = fnv.getParamMap();

        List<String> allFunctionNames = new ArrayList<>(functionNames);

        if (options.functionName != null) {
            if (!options.functionName.endsWith("Verification")) {
                options.functionName = options.functionName + "Verification";
            }
            functionNames = functionNames.stream().filter(f -> f.contains("." + options.functionName + ":")).toList();
            if (functionNames.isEmpty()) {
                warn("Function " + options.functionName + " could not be found in the specified file.");
                warn("Found the following functions: " + allFunctionNames);
                return;
            }
        }
        info("Run jbmc for " + functionNames.size() + " functions.");

        for (String functionName : functionNames) {
            if (options.isWindows()) {
                if (functionName.contains("()")) {
                    functionName = functionName.replace("<init>", "<clinit>");
                }
                functionName = "\"" + functionName + "\"";
            }

            try (ExecutorService executerService = Executors.newFixedThreadPool(1)) {
                String finalFunctionName = functionName;
                Runnable worker = () -> runJBMC(finalFunctionName, paramMap);
                final Future<?> handler = executerService.submit(worker);
                handler.get(options.timeout, TimeUnit.MILLISECONDS);
            } catch (TimeoutException e) {
                if (jbmcProcess != null) {
                    jbmcProcess.destroyForcibly();
                }
                info(YELLOW_BOLD + "JBMC call for function " + functionName + " timed out." + RESET + "\n");
            } catch (InterruptedException | ExecutionException e) {
                e.printStackTrace();
            }
        }
    }

    public void printOutput(@Nullable JBMCOutput output, long time, String functionName) {
        if (output == null) {
            options.keepTranslation = true;
            error("Error parsing xml-output of JBMC.");
            return;
        }
        if (options.doSanityCheck) {
            if (output.printStatus().contains("SUCC")) {
                warn("Sanity check failed for: " + functionName);
            } else {
                info("Sanity check ok for function: " + functionName);
            }
            return;
        }
        info("Result for function " + functionName + ":");
        if (options.timed) {
            info("JBMC took " + time + "ms.");
        }


        if (output.getErrors().isEmpty()) {
            if (options.runWithTrace) {
                String traces = output.printAllTraces();
                if (!traces.isEmpty()) {
                    info(traces);
                }
            }
            //Arrays.stream(traces.split("\n")).forEach(s -> log.info(s));
            String status = output.printStatus();
            if (status.contains("SUCC")) {
                info(GREEN_BOLD + status + RESET);
            } else {
                info(RED_BOLD + status + RESET);
            }
        } else {
            options.keepTranslation = true;
            error(output.printErrors());
        }
    }

    public void runJBMC(String functionName, Map<String, List<String>> paramMap) {
        try {
            debug("Running jbmc for function: " + functionName);
            String classFile = options.getTmpFile().getFileName().toString().replace(".java", "");
            classFile = classFile.substring(classFile.lastIndexOf(File.separator + "tmp") + 5);
            //classFile = "." + classFile;

            ArrayList<String> tmp = new ArrayList<>();
            if (options.isWindows()) {
                tmp.add("cmd.exe");
                tmp.add("/c");
                classFile = classFile.replaceAll("\\\\", "/");
            }
            tmp.add("jbmc");
            tmp.add(classFile);
            tmp.add("--function");
            tmp.add(functionName);
            tmp.add("--unwind");
            tmp.add(String.valueOf(options.getUnwinds()));
            tmp.add("--max-nondet-array-length");
            tmp.add(String.valueOf(options.getMaxArraySize()));

            jbmcOptions = prepareJBMCOptions(options.getJbmcOptions());
            tmp.addAll(options.getJbmcOptions());
            tmp.add("--xml-ui");
            //tmp.add("--cp");
            String libPath = System.getProperty("java.library.path");
            //tmp.add(libPath);
            String[] commands = new String[tmp.size()];
            commands = tmp.toArray(commands);

            debug(Arrays.toString(commands));
            Runtime rt = Runtime.getRuntime();
            rt.addShutdownHook(new Thread(() -> {
                try {
                    cleanUp();
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }
            }));
            long start = System.currentTimeMillis();

            jbmcProcess = rt.exec(commands, null, options.getTmpFolder().toFile());


            BufferedReader stdInput = new BufferedReader(new
                    InputStreamReader(jbmcProcess.getInputStream()));

            BufferedReader stdError = new BufferedReader(new
                    InputStreamReader(jbmcProcess.getErrorStream()));


            StringBuilder sb = new StringBuilder();
            String line = stdInput.readLine();
            while (line != null) {
                sb.append(line);
                sb.append(System.lineSeparator());
                line = stdInput.readLine();
            }

            if (Thread.interrupted()) {
                return;
            }

            //Has to stay down here otherwise not reading the output may block the process
            jbmcProcess.waitFor();
            long end = System.currentTimeMillis();

            String xmlOutput = sb.toString();
            //String error = sb2.toString();


            if ((jbmcProcess.exitValue() != 0 && jbmcProcess.exitValue() != 10) || options.keepTranslation) {
                options.keepTranslation = true;
                Files.writeString(options.getTmpFolder().toAbsolutePath().resolve("xmlout.xml"), xmlOutput);
                if (jbmcProcess.exitValue() != 0 && jbmcProcess.exitValue() != 10) {
                    error("JBMC did not terminate as expected for function: " + functionName +
                            "\nif ran with -kt option jbmc output can be found in xmlout.xml in the tmp folder");
                    return;
                }
            } else {
                debug("JBMC terminated normally.");
            }

            if ((options.isFullTraceRequested() || !options.getRelevantVars().isEmpty()) && !options.runWithTrace) {
                options.runWithTrace = true;
                warn("Options concerning the trace where found but not -tr option was given. \"-tr\" was automatically added.");
            }

            if (xmlOutput.startsWith("<?xml version=\"1.0\" encoding=\"UTF-8\"?>")) {
                long start1 = System.currentTimeMillis();
                JBMCOutput output = TraceParser.parse(xmlOutput, options.runWithTrace);
                printOutput(output, end - start, functionName);
                long duration = System.currentTimeMillis() - start1;
                debug("Parsing xml took: " + duration + "ms.");
            } else {
                error("Unexpected jbmc output:");
                error(xmlOutput);
            }
        } catch (Exception e) {
            error("Error running jbmc.");
            options.keepTranslation = true;
            e.printStackTrace();
        }
    }

    public void cleanUp() throws IOException {
        if (!didCleanUp && !options.keepTranslation) {
            deleteFolder(options.getTmpFolder(), false);
            if (!options.keepTranslation) {
                try {
                    Files.deleteIfExists(options.getTmpFolder());
                } catch (IOException e) {
                    //log.info("Could not delete tmp folder.");
                }
            }
        }
        didCleanUp = true;
    }

    public static void deleteFolder(Path folder, boolean all) throws IOException {
        if (Files.exists(folder)) {
            try (var walk = Files.walk(folder)) {
                walk.sorted(Comparator.reverseOrder())
                        .forEach(path -> {
                            try {
                                Files.deleteIfExists(path);
                            } catch (IOException ignored) {
                            }
                        });
            }
        }
        /*File[] tmpFiles = folder.listFiles();
        if (tmpFiles != null) {
            for (File f : tmpFiles) {
                if (!keepTranslation || fileName != null && !f.getName().endsWith(new File(fileName).getName()) || all) {
                    if (f.isDirectory()) {
                        if (!f.getName().contains("testannotations")) {
                            deleteFolder(f, all);
                        }
                    }
                    try {
                        if (f.exists()) {
                            Files.delete(f.toPath());
                        }
                    } catch (IOException ex) {
                        //log.info("Could not delete temporary file: " + f.getAbsolutePath());
                    }
                }
            }
        }*/
    }

    public static CompilationUnit rewriteAssert(CompilationUnit cu, JJBMCOptions options) {
        return Jml2JavaFacade.translate(cu, options);
    }

    private boolean verifyJavaVersion(String binary) {
        String[] commands = new String[]{binary, "-version"};
        Process p;
        try {
            ProcessBuilder pb = new ProcessBuilder().command(commands)
                    .redirectErrorStream(true);
            p = pb.start();
            BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()));
            String line = reader.readLine();
            if (line != null) {
                return line.contains("1.8");
            }
        } catch (IOException e) {
            return false;
        }
        return false;
    }

    @Override
    public Integer call() throws Exception {
        if (options.isDebugMode()) {
            setDebugOn();
            options.setKeepTranslation(true);
        }
        if (options.forceInlining) {
            options.forceInliningLoops = true;
            options.forceInliningMethods = true;
        }

        var f = options.getFileName();
        translateAndRunJBMC();
        if (options.doSanityCheck) {
            options.doSanityCheck = false;
            translateAndRunJBMC();
        }
        return 0;
    }


}
