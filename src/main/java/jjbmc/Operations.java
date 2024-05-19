package jjbmc;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.google.common.collect.ImmutableList;
import jjbmc.jml2java.Jml2JavaFacade;
import jjbmc.trace.TraceParser;
import lombok.Getter;
import lombok.RequiredArgsConstructor;
import org.jspecify.annotations.Nullable;

import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;

import static jjbmc.ErrorLogger.*;
import static jjbmc.ErrorLogger.setDebugOn;

@RequiredArgsConstructor
@Getter
public class Operations implements Callable<Integer> {
    private final JBMCOptions options;
    @Nullable private Process jbmcProcess;

    public static CompilationUnit translate(File file, boolean forceInliningMethods) throws Exception {
        return translate(forceInliningMethods, file.toPath());
    }

    public static CompilationUnit translate(boolean forceInliningMethods, Path... fileNames) throws Exception {
        ParserConfiguration config = new ParserConfiguration();
        config.setJmlKeys(ImmutableList.of(ImmutableList.of("openjml")));
        config.setProcessJml(true);
        JavaParser parser = new JavaParser(config);

        List<CompilationUnit> compilationUnits = new ArrayList<>(32);
        for (var arg : fileNames) {
            ParseResult<CompilationUnit> result = parser.parse(arg);
            if (result.isSuccessful()) {
                compilationUnits.add(result.getResult().get());
            } else {
                System.out.println(arg);
                result.getProblems().forEach(System.out::println);
            }
        }

        for (var it : compilationUnits) {
            try {
                return rewriteAssert(it, forceInliningMethods);
                //return api.prettyPrint(t);
            } catch (UnsupportedException e) {
                error(e.getMessage());
                return null;
            } catch (TranslationException e) {
                error(e.getMessage());
                return null;
            }
        }
        return null;
    }

    public void translateAndRunJBMC(Path file, String functionName) throws Exception {
        options.functionName = functionName;
        options.setFileName(file.toString());
        translateAndRunJBMC(file);
    }

    public Path prepareForJBMC(Path fileName) throws Exception {
        options.setDidCleanUp(false);

        if (options.unwinds < 0) {
            info("No unwind argument found. Default to 7.");
            options.unwinds = 7;
        }
        if (options.getMaxArraySize() < 0) {
            info("No maxArraySize argument found. Default to " + (options.unwinds - 2) + ".");
            options.setMaxArraySize(Math.max(options.unwinds - 2, 0));
        }
        if (options.getMaxArraySize() > options.unwinds - 2) {
            warn("Unwinds is set to less than maxArraySize + 2. This may lead to unsound behaviour.");
        }

        try {
            if (!Files.exists(fileName)) {
                throw new FileNotFoundException("Could not find file " + fileName);
            }

            options.setTmpFolder(fileName.resolveSibling("tmp"));
            deleteFolder(options.getTmpFolder(), true);
            Files.createDirectories(options.getTmpFolder());

            options.setTmpFile(options.getTmpFolder().resolve(fileName.getFileName()));
            var tmpClassFile = options.getTmpFolder().resolve(
                    fileName.getFileName().toString()
                            .replace(".java", ".class"));

            Files.deleteIfExists(options.getTmpFile());
            Files.deleteIfExists(tmpClassFile);

            Files.copy(fileName, options.getTmpFile(), StandardCopyOption.REPLACE_EXISTING);
            for (String s : options.libFiles) {
                var tmpF = fileName.resolveSibling(s);
                if (!Files.exists(tmpF)) {
                    throw new FileNotFoundException("Could not find libFile: " + tmpF);
                } else {
                    Files.copy(tmpF,
                            options.getTmpFolder().resolve(tmpF.getFileName()),
                            StandardCopyOption.REPLACE_EXISTING);
                }
            }

            createCProverFolder(options.getTmpFolder().toAbsolutePath());
            long start = System.currentTimeMillis();
            var translation = translate(this.options.forceInliningMethods, options.getTmpFile());
            long finish = System.currentTimeMillis();
            debug("Translation.Translation took: " + (finish - start) + "ms");

            if (translation != null) {
                String packageName = translation.getPackageDeclaration()
                        .map(NodeWithName::getNameAsString).orElse("");
                Files.deleteIfExists(options.getTmpFile());
                packageName = packageName.replace(".", "/");
                var packageFolder = options.getTmpFolder().resolve(packageName);
                Files.createDirectories(packageFolder);
                options.setTmpFile(packageFolder.resolve(options.getTmpFile().getFileName()));
                var content = pprint(translation);
                Files.writeString(options.getTmpFile(), content, StandardOpenOption.CREATE);
            } else {
                return null;
            }
        } catch (Exception e) {
            options.keepTranslation = true;
            cleanUp();
            debug(e);
            throw e;
        }

        try {
            String[] commands = new String[options.apiArgs.length + 3];
            commands[0] = options.javacBin;
            commands[1] = "-g";
            commands[2] = options.getTmpFile().toAbsolutePath().toString();
            System.arraycopy(options.apiArgs, 0, commands, 3, options.apiArgs.length);
            debug("Compiling translated file: " + Arrays.toString(commands));
            ProcessBuilder pb = new ProcessBuilder().command(commands)
                    .redirectOutput(options.getTmpFolder().resolve("compilationErrors.txt").toFile())
                    .redirectErrorStream(true)
                    .directory(options.getTmpFolder().toFile());
            Process proc = pb.start();

            proc.waitFor();
            if (proc.exitValue() != 0) {
                options.keepTranslation = true;
                error("Compilation failed. See compilationErrors.txt for javac output.");
                return null;
            }
        } catch (IOException | InterruptedException e) {
            options.keepTranslation = true;
            error("Error during preparation.");
            e.printStackTrace();
        }

        debug("Compilation successful.");
        if (!JbmcFacade.verifyJBMCVersion(options.jbmcBin, options.isWindows())) {
            throw new Exception("Unverified JBMC version");
        }
        return options.getTmpFile();
    }

    private static String pprint(Node translation) {
        DefaultPrettyPrinter pp = new DefaultPrettyPrinter(
                MyPPrintVisitor::new, new DefaultPrinterConfiguration());
        return pp.print(translation);
    }

    public void translateAndRunJBMC(Path fileName) throws Exception {
        var tmpFile = prepareForJBMC(fileName);
        //TODO FunctionNameVisitor.parseFile(tmpFile.getAbsolutePath());
        List<String> functionNames = null;//FunctionNameVisitor.getFunctionNames();
        Map<String, List<String>> paramMap = null;// FunctionNameVisitor.getParamMap();

        List<String> allFunctionNames = new ArrayList<>(functionNames);
        if (options.functionName != null) {
            if (!options.functionName.endsWith("Verf")) {
                options.functionName = options.functionName + "Verf";
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
            ExecutorService executerService = Executors.newSingleThreadExecutor();
            String finalFunctionName = functionName;
            Runnable worker = () -> runJBMC(tmpFile, finalFunctionName, paramMap);

            final Future<?> handler = executerService.submit(worker);
            try {
                handler.get(options.timeout, TimeUnit.MILLISECONDS);
            } catch (TimeoutException e) {
                handler.cancel(true);
                jbmcProcess.destroyForcibly();
                info(YELLOW_BOLD + "JBMC call for function " + functionName + " timed out." + RESET + "\n");
            } catch (InterruptedException | ExecutionException e) {
                e.printStackTrace();
            }
            executerService.shutdownNow();
        }
    }

    private static List<String> prepareJBMCOptions(List<String> options) {
        List<String> res = new ArrayList<>();
        for (String s : options) {
            res.addAll(Arrays.asList(s.split(" ")));
        }
        return res;
    }

    public void runJBMC(Path tmpFile, String functionName, Map<String, List<String>> paramMap) {
        try {
            debug("Running jbmc for function: " + functionName);
            //commands = new String[] {"jbmc", tmpFile.getAbsolutePath().replace(".java", ".class")};
            String classFile = tmpFile.getFileName().toString().replace(".java", "");
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
            tmp.add(String.valueOf(options.unwinds));
            tmp.add("--max-nondet-array-length");
            tmp.add(String.valueOf(options.getMaxArraySize()));

            jbmcOptions = prepareJBMCOptions(options.jbmcOptions);
            tmp.addAll(options.jbmcOptions);
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

            jbmcProcess = rt.exec(commands, null, options.tmpFolder.toFile());


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
                Files.writeString(options.tmpFolder.toAbsolutePath().resolve("xmlout.xml"), xmlOutput);
                if (jbmcProcess.exitValue() != 0 && jbmcProcess.exitValue() != 10) {
                    error("JBMC did not terminate as expected for function: " + functionName +
                            "\nif ran with -kt option jbmc output can be found in xmlout.xml in the tmp folder");
                    return;
                }
            } else {
                debug("JBMC terminated normally.");
            }

            if ((options.fullTraceRequested || !options.relevantVars.isEmpty()) && !options.runWithTrace) {
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

    private static void createCProverFolder(Path fileName) throws IOException {
        var dir = fileName.resolve("org/cprover");
        debug("Copying CProver.java to {}", dir.toAbsolutePath());
        Files.createDirectories(dir);
        try (InputStream is = JBMCOptions.class.getResourceAsStream("/cli/CProver.java")) {
            Files.copy(Objects.requireNonNull(is), dir.resolve("CProver.java"));
        }
    }

    public void cleanUp() throws IOException {
        if (!options.didCleanUp && !options.keepTranslation) {
            deleteFolder(options.tmpFolder, false);
            if (!options.keepTranslation) {
                try {
                    Files.deleteIfExists(options.tmpFolder);
                } catch (IOException e) {
                    //log.info("Could not delete tmp folder.");
                }
            }
        }
        options.didCleanUp = true;
    }

    public static void deleteFolder(Path folder, boolean all) throws IOException {
        try (var walk = Files.walk(folder)) {
            walk.sorted(Comparator.reverseOrder())
                    .forEach(path -> {
                        try {
                            Files.deleteIfExists(path);
                        } catch (IOException ignored) {
                        }
                    });
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

    public static CompilationUnit rewriteAssert(CompilationUnit cu, boolean forceInliningMethods) {
        return Jml2JavaFacade.translate(cu, forceInliningMethods);
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

        var f = Paths.get(options.getFileName());
        translateAndRunJBMC(f);
        if (options.doSanityCheck) {
            options.doSanityCheck = false;
            translateAndRunJBMC(f);
        }
        return 0;
    }


}
