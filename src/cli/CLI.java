package cli;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.google.common.collect.ImmutableList;
import exceptions.TranslationException;
import exceptions.UnsupportedException;
import org.apache.logging.log4j.Level;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.apache.logging.log4j.core.config.Configurator;
import translation.FunctionNameVisitor;
import translation.jml2java.Jml2JavaFacade;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static picocli.CommandLine.*;


/**
 * Created by jklamroth on 1/15/19.
 */

@Command(name = "openJBMC", header = "@|bold openJBMC Bounded Model checking for JML|@")
public class CLI implements Runnable {
    public static final String RESET = "\033[0m";  // Text Reset
    public static final String RED_BOLD = "\033[1;31m";    // RED
    public static final String GREEN_BOLD = "\033[1;32m";  // GREEN
    public static final String YELLOW_BOLD = "\033[1;33m"; // YELLOW
    private static final Logger log = LogManager.getLogger(CLI.class);
    private static final int jbmcMajorVer = 5;
    private static final int jbmcMinorVer = 22;
    public static String[] apiArgs = new String[0];
    @Option(names = {"-kt", "-keepTranslation"}, description = "Keep the temporary file which contains the translation of the given file.")
    public static boolean keepTranslation = false;
    @Option(names = {"-fi", "-forceInlining"},
            description = "Inline methods and unroll loops even if a contract is available")
    public static boolean forceInlining;
    @Option(names = {"-fil", "-forceInliningLoopsOnly"},
            description = "Unroll loops even if a loop contract is available")
    public static boolean forceInliningLoops;
    @Option(names = {"-fim", "-forceInliningMethodsOnly"},
            description = "Inline methods even if a method contract is available")
    public static boolean forceInliningMethods;
    @Option(names = {"-c", "-clock"},
            description = "Print out timing information.")
    public static boolean timed;
    @Option(names = {"-dsa", "-dontsplitasserts"},
            description = "Split assertions if possible.")
    public static boolean splitAssertions = true;
    @Option(names = {"-t", "-timeout"},
            description = "Provide a timeout in ms for each jbmc call. (default 10s)",
            arity = "0..1")
    public static int timeout = 10000;
    @Option(names = {"-u", "-unwind"},
            description = "Number of times loops are unwound. (default 5)",
            arity = "0..1")
    public static int unwinds = -1;
    @Option(names = {"-tr", "-trace"},
            description = "Prints out traces for failing pvcs.")
    public static boolean runWithTrace = false;
    @Option(names = {"-jbmc", "-jbmcBinary"},
            description = "allows to set the jbmc binary that is used for the verification (has to be relative or absolute path no alias)")
    public static String jbmcBin = "jbmc";
    @Option(names = {"-lf", "--libFiles"},
            description = "Files to be copied to the translation folder.")
    public static String[] libFiles = new String[]{};
    @Option(names = {"-jc", "-javac"},
            description = "allows to set the javac binary that is used for compilation of source files manually")
    public static String javacBin = "javac";
    @Option(names = {"-ci", "-contractIndex"},
            description = "Allows to specify which of the contracts is going to be specified index from 0 upwards",
            arity = "0..1")
    public static int caseIdx = 0;
    @Option(names = {"-mas", "-maxArraySize"},
            description = "Sets the maximum size more nondeterministic arrays.",
            arity = "0..1")
    public static int maxArraySize = -1;
    @Option(names = {"-sc", "-sanityCheck"},
            description = "Adds a check for each method if assumptions are equals to false.",
            arity = "0..1")
    public static boolean doSanityCheck = false;
    @Option(names = {"-d", "-debug"},
            description = "Runs JJBMC in debug mode. More outputs and preventing clean up of temporary files.")
    public static boolean debugMode = false;
    public static Map<String, String> expressionMap = new HashMap<>();
    @Parameters(index = "0", arity = "1", description = "The file containing methods to be verified.")
    static String fileName = null;
    @Parameters(index = "1", arity = "0..1", description = "The method to be verified. If not provided -va is automatically added.")
    public static String functionName = null;
    @Option(names = {"-j", "-jbmcOptions"}, description = "Options to be passed to jbmc.")
    static List<String> jbmcOptions = new ArrayList<>();
    @Option(names = {"-h", "-help"}, usageHelp = true,
            description = "Print usage help and exit.")
    static boolean usageHelpRequested;
    @Option(names = {"-rv", "-relevantVar"},
            description = "Names of variables whos values should be printed in a trace. (Has to be run with -tr option)")
    public static List<String> relevantVars = new ArrayList<>();
    @Option(names = {"-ft", "-fullTrace"}, description = "Prevents traces from being filtered for relevant variables and prints all values. " +
            "(Has to be run with -tr option)")
    public static boolean fullTraceRequested = false;

    @Option(names = {"-pp", "-proofPreconditions"}, description = "Adds additional assertions proving the preconditions " +
            "of called methods while still inlining them. (implies -fim option)")
    public static boolean proofPreconditions = false;
    static File tmpFolder = null;
    private static boolean didCleanUp = false;
    private static Process jbmcProcess = null;
    private static File tmpFile;
    private static final boolean isWindows = System.getProperty("os.name")
            .toLowerCase().startsWith("windows");
    private static List<String> functionNames;


    public static void reset() {
        timeout = 10000;
        timed = false;
        debugMode = false;
        keepTranslation = false;
        functionName = null;
        forceInlining = false;
        forceInliningMethods = false;
        forceInliningLoops = false;
        runWithTrace = false;
        unwinds = -1;
        maxArraySize = -1;
        caseIdx = 0;
        jbmcOptions = new ArrayList<>();
        fullTraceRequested = false;
        relevantVars = new ArrayList<>();
    }

    public static CompilationUnit translate(File file) throws Exception {
        return translate(file.toPath());
    }

    public static CompilationUnit translate(Path fileName) throws Exception {
        ParserConfiguration config = new ParserConfiguration();
        config.setJmlKeys(ImmutableList.of(ImmutableList.of("openjml")));
        config.setProcessJml(true);
        //TODO this should be checked if this is fine
        config.setSymbolResolver(new JavaSymbolSolver(new JavaParserTypeSolver(fileName.getParent())));
        JavaParser parser = new JavaParser(config);

        List<CompilationUnit> compilationUnits = new ArrayList<>(32);
        ParseResult<CompilationUnit> result = parser.parse(fileName);
        if (result.isSuccessful()) {
            compilationUnits.add(result.getResult().get());
        } else {
            System.out.println(fileName);
            result.getProblems().forEach(System.out::println);
        }


        for (var it : compilationUnits) {
            functionNames = new ArrayList<>();
            it.accept(new FunctionNameVisitor(), functionNames);
            try {
                return rewriteAssert(it);
                //return api.prettyPrint(t);
            } catch (UnsupportedException e) {
                log.error(e.getMessage());
                if (debugMode) {
                    e.printStackTrace();
                }
                return null;
            } catch (TranslationException e) {
                log.error(e.getMessage());
                if (debugMode) {
                    e.printStackTrace();
                }
                return null;
            }
        }
        return null;
    }

    public static void translateAndRunJBMC(String file, String functionName) {
        CLI.functionName = functionName;
        fileName = file;
        translateAndRunJBMC(file);
    }

    public static File prepareForJBMC(String fileName) {
        didCleanUp = false;

        if (unwinds < 0) {
            log.info("No unwind argument found. Default to 7.");
            unwinds = 7;
        }
        if (maxArraySize < 0) {
            log.info("No maxArraySize argument found. Default to " + (unwinds - 2) + ".");
            maxArraySize = Math.max(unwinds - 2, 0);
        }
        if (maxArraySize > unwinds - 2) {
            log.warn("Unwinds is set to less than maxArraySize + 2. This may lead to unsound behaviour.");
        }

        try {
            File f = new File(fileName);
            if (!f.exists()) {
                log.error("Could not find file " + f);
                return null;
            }
            tmpFolder = new File(f.getParentFile(), "tmp");
            deleteFolder(tmpFolder, true);
            tmpFolder.mkdirs();
            tmpFile = new File(tmpFolder, f.getName());
            File tmpClassFile = new File(tmpFolder, f.getName().replace(".java", ".class"));
            if (tmpFile.exists()) {
                tmpFile.delete();
            }
            if (tmpClassFile.exists()) {
                tmpClassFile.delete();
            }
            Files.copy(f.toPath(), tmpFile.toPath(), StandardCopyOption.REPLACE_EXISTING);
            for (String s : libFiles) {
                File tmpF = new File(f.getParentFile(), s);
                if (!tmpF.exists()) {
                    log.error("Could not find libFile: " + tmpF);
                    return null;
                }
                Files.copy(tmpF.toPath(), new File(tmpFolder, tmpF.getName()).toPath(), StandardCopyOption.REPLACE_EXISTING);
            }

            createCProverFolder(tmpFolder.getAbsolutePath());
            long start = System.currentTimeMillis();
            var translation = translate(tmpFile);
            long finish = System.currentTimeMillis();
            log.debug("Translation.Translation took: " + (finish - start) + "ms");

            if (translation != null) {
                String packageName = translation.getPackageDeclaration()
                        .map(NodeWithName::getNameAsString).orElse("");

                if (tmpFile.exists()) {
                    Files.delete(tmpFile.toPath());
                }
                if (packageName != null) {
                    packageName = packageName.replace(".", "/");
                }
                File packageFolder = new File(tmpFolder, packageName);
                packageFolder.mkdirs();
                tmpFile = new File(packageFolder, tmpFile.getName());
                var content = pprint(translation);
                Files.write(tmpFile.toPath(), content.getBytes(StandardCharsets.UTF_8), StandardOpenOption.CREATE);
            } else {
                return null;
            }
        } catch (Exception e) {
            keepTranslation = true;
            cleanUp();
            if (debugMode) {
                e.printStackTrace();
            }
            log.error(e.getMessage());
            return null;
        }

        try {
            String[] commands = new String[apiArgs.length + 3];
            /*if (!verifyJavaVersion(javacBin)) {
                log.error("The provided javac version doesn't seem to be a valid java 8 compiler. " +
                        "Please make sure that the default javac is version 8 or provide a path to a javac binary manually via the option -javac.");
                return null;
            }*/

            commands[0] = javacBin;
            commands[1] = "-g";
            commands[2] = tmpFile.getAbsolutePath();
            System.arraycopy(apiArgs, 0, commands, 3, apiArgs.length);
            log.debug("Compiling translated file: " + Arrays.toString(commands));
            ProcessBuilder pb = new ProcessBuilder().command(commands)
                    .redirectOutput(new File(tmpFolder, "compilationErrors.txt"))
                    .redirectErrorStream(true)
                    .directory(tmpFolder);
            Process proc = pb.start();

            proc.waitFor();
            if (proc.exitValue() != 0) {
                keepTranslation = true;
                log.error("Compilation failed. See compilationErrors.txt for javac output.");
                return null;
            }
        } catch (IOException | InterruptedException e) {
            keepTranslation = true;
            log.error("Error during preparation.");
            e.printStackTrace();
        }


        //cleanUp();
        log.debug("Complilation sucessfull.");
        if (!verifyJBMCVersion()) {
            return null;
        }
        return tmpFile;
    }

    private static String pprint(Node translation) {
        DefaultPrettyPrinter pp = new DefaultPrettyPrinter(
                MyPPrintVisitor::new, new DefaultPrinterConfiguration());
        return pp.print(translation);
    }

    private static boolean verifyJBMCVersion() {
        try {
            String[] commands = new String[]{jbmcBin};
            if (isWindows) {
                commands = new String[]{"cmd.exe", "/c", jbmcBin};
            }

            Runtime rt = Runtime.getRuntime();

            Process process = rt.exec(commands);

            BufferedReader stdInput = new BufferedReader(new
                    InputStreamReader(process.getInputStream()));

            BufferedReader stdError = new BufferedReader(new
                    InputStreamReader(process.getErrorStream()));

            StringBuilder sb = new StringBuilder();
            String line = stdInput.readLine();
            while (line != null) {
                sb.append(line);
                sb.append(System.getProperty("line.separator"));
                line = stdInput.readLine();
            }

            String sb2 = "";
            String line2 = stdInput.readLine();
            while (line2 != null) {
                sb.append(line);
                sb.append(System.getProperty("line.separator"));
                line = stdError.readLine();
            }

            //Has to stay down here otherwise not reading the output may block the process
            process.waitFor();

            String output = sb.toString();
            String error = sb2;
            if (output.toLowerCase().contains("jbmc version")) {
                log.debug("Found valid jbmc version: " + output);
                Pattern pattern = Pattern.compile("jbmc version (\\d*)\\.(\\d*)\\.(\\d*)? \\(", Pattern.CASE_INSENSITIVE);
                Matcher matcher = pattern.matcher(output);
                boolean matchFound = matcher.find();
                if (Integer.parseInt(matcher.group(1)) < jbmcMajorVer) {
                    log.error("Error validating jbmc binary \"" + jbmcBin + "\"");
                    log.error("Found version: " + output);
                    log.error("but at least version " + jbmcMajorVer + "." + jbmcMinorVer + " is required.");
                    log.error("Either install jbmc and make sure it is included in the path or provide " +
                            "a jbmc binary manually with the -jbmcBinary option");
                    log.error("To install jbmc (as part of cbmc) head to https://github.com/diffblue/cbmc/releases/ ");
                    return false;
                } else if (Integer.parseInt(matcher.group(2)) < jbmcMinorVer) {
                    log.error("Error validating jbmc binary \"" + jbmcBin + "\"");
                    log.error("Found version: " + output);
                    log.error("but at least version " + jbmcMajorVer + "." + jbmcMinorVer + " is required.");
                    log.error("Either install jbmc and make sure it is included in the path or provide " +
                            "a jbmc binary manually with the -jbmcBinary option");
                    log.error("To install jbmc (as part of cbmc) head to https://github.com/diffblue/cbmc/releases/ ");
                    return false;
                }
                return true;
            }
        } catch (IOException | InterruptedException e) {
            keepTranslation = true;
            log.error("Error validating jbmc binary \"" + jbmcBin + "\" (" + e.getMessage() + ")");
            log.error("Either install jbmc and make sure it is included in the path or provide a jbmc binary manually with the -jbmcBinary option");
            log.error("To install jbmc (as part of cbmc) head to https://github.com/diffblue/cbmc/releases/ ");
            //e.printStackTrace();
            return false;
        }
        log.error("Error validating jbmc binary \"" + jbmcBin + "\"");
        log.error("Either install jbmc and make sure it is included in the path or provide a jbmc binary manually with the -jbmcBinary option");
        log.error("To install jbmc (as part of cbmc) head to https://github.com/diffblue/cbmc/releases/ ");
        return true;
    }

    public static void translateAndRunJBMC(String fileName) {
        File tmpFile = prepareForJBMC(fileName);
        if (tmpFile == null) {
            keepTranslation = true;
            log.error("Error preparing translation. Abort verification.");
            return;
        }
        log.debug("Parse function names.");


        List<String> allFunctionNames = functionNames;
        if (functionName != null) {
            //functionNames = functionNames.stream().filter(f -> f.contains("." + functionName + ":")).collect(Collectors.toList());
            functionNames = functionNames.stream().filter(f -> f.contains("." + functionName)).collect(Collectors.toList());
            if (functionNames.size() == 0) {
                log.warn("Function " + functionName + " could not be found in the specified file.");
                log.warn("Found the following functions: " + allFunctionNames);
                return;
            }
        }
        log.info("Run jbmc for " + functionNames.size() + " functions.");

        for (String functionName : functionNames) {
            if (!functionName.endsWith("Verification")) {
                functionName = functionName + "Verification";
            }
            if (isWindows) {
                if (functionName.contains("()")) {
                    functionName = functionName.replace("<init>", "<clinit>");
                }
                functionName = "\"" + functionName + "\"";
            }
            ExecutorService executerService = Executors.newSingleThreadExecutor();
            String finalFunctionName = functionName;
            Runnable worker = () -> runJBMC(tmpFile, finalFunctionName);

            final Future handler = executerService.submit(worker);
            try {
                handler.get(timeout, TimeUnit.MILLISECONDS);
            } catch (TimeoutException e) {
                handler.cancel(true);
                jbmcProcess.destroyForcibly();
                log.info(YELLOW_BOLD + "JBMC call for function " + functionName + " timed out." + RESET + "\n");
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

    public static void runJBMC(File tmpFile, String functionName) {
        try {
            log.debug("Running jbmc for function: " + functionName);
            //commands = new String[] {"jbmc", tmpFile.getAbsolutePath().replace(".java", ".class")};
            String classFile = tmpFile.getAbsolutePath().replace(".java", "");
            classFile = classFile.substring(classFile.lastIndexOf(File.separator + "tmp") + 5);
            //classFile = "." + classFile;

            ArrayList<String> tmp = new ArrayList<>();
            if (isWindows) {
                tmp.add("cmd.exe");
                tmp.add("/c");
                classFile = classFile.replaceAll("\\\\", "/");
            }
            tmp.add("jbmc");
            tmp.add(classFile);
            tmp.add("--function");
            tmp.add(functionName);
            tmp.add("--unwind");
            tmp.add(String.valueOf(unwinds));
            tmp.add("--max-nondet-array-length");
            tmp.add(String.valueOf(maxArraySize));

            jbmcOptions = prepareJBMCOptions(jbmcOptions);
            tmp.addAll(jbmcOptions);
            tmp.add("--xml-ui");
            //tmp.add("--cp");
            String libPath = System.getProperty("java.library.path");
            //tmp.add(libPath);
            String[] commands = new String[tmp.size()];
            commands = tmp.toArray(commands);

            log.debug(Arrays.toString(commands));
            Runtime rt = Runtime.getRuntime();
            rt.addShutdownHook(new Thread(CLI::cleanUp));
            long start = System.currentTimeMillis();

            jbmcProcess = rt.exec(commands, null, tmpFolder);


            BufferedReader stdInput = new BufferedReader(new
                    InputStreamReader(jbmcProcess.getInputStream()));

            BufferedReader stdError = new BufferedReader(new
                    InputStreamReader(jbmcProcess.getErrorStream()));


            StringBuilder sb = new StringBuilder();
            String line = stdInput.readLine();
            while (line != null) {
                sb.append(line);
                sb.append(System.getProperty("line.separator"));
                line = stdInput.readLine();
            }

            //StringBuilder sb2 = new StringBuilder();
            //String line2 = stdError.readLine();
            //while (line2 != null) {
            //    sb2.append(line);
            //    sb2.append(System.getProperty("line.separator"));
            //    line = stdError.readLine();
            //}


            if (Thread.interrupted()) {
                return;
            }

            //Has to stay down here otherwise not reading the output may block the process
            jbmcProcess.waitFor();
            long end = System.currentTimeMillis();

            String xmlOutput = sb.toString();
            //String error = sb2.toString();


            if ((jbmcProcess.exitValue() != 0 && jbmcProcess.exitValue() != 10) || keepTranslation) {
                keepTranslation = true;
                Files.write(Paths.get(tmpFolder.getAbsolutePath(), "xmlout.xml"), xmlOutput.getBytes());
                if (jbmcProcess.exitValue() != 0 && jbmcProcess.exitValue() != 10) {
                    log.error("JBMC did not terminate as expected for function: " + functionName +
                            "\nif ran with -kt option jbmc output can be found in xmlout.xml in the tmp folder");
                    return;
                }
            } else {
                log.debug("JBMC terminated normally.");
            }

            if ((fullTraceRequested || relevantVars.size() > 0) && !runWithTrace) {
                runWithTrace = true;
                log.warn("Options concerning the trace where found but not -tr option was given. \"-tr\" was automatically added.");
            }

            if (xmlOutput.startsWith("<?xml version=\"1.0\" encoding=\"UTF-8\"?>")) {
                long start1 = System.currentTimeMillis();
                //JBMCOutput output = TraceParser.parse(xmlOutput, runWithTrace);
                JBMCOutput output = TraceParser.parse(xmlOutput, false);
                printOutput(output, end - start, functionName);
                long duration = System.currentTimeMillis() - start1;
                log.debug("Parsing xml took: " + duration + "ms.");
            } else {
                log.error("Unexpected jbmc output:");
                log.error(xmlOutput);
            }
        } catch (Exception e) {
            log.error("Error running jbmc.");
            keepTranslation = true;
            e.printStackTrace();
        }
    }

    public static void printOutput(JBMCOutput output, long time, String functionName) {
        if (output == null) {
            keepTranslation = true;
            log.error("Error parsing xml-output of JBMC.");
            return;
        }
        if (doSanityCheck) {
            if (output.printStatus().contains("SUCC")) {
                log.warn("Sanity check failed for: " + functionName);
            } else {
                log.info("Sanity check ok for function: " + functionName);
            }
            return;
        }
        log.info("Result for function " + functionName + ":");
        if (timed) {
            log.info("JBMC took " + time + "ms.");
        }


        if (output.errors.size() == 0) {
            if (runWithTrace) {
                String traces = output.printAllTraces();
                if (!traces.isEmpty()) {
                    log.info(traces);
                }
            }
            //Arrays.stream(traces.split("\n")).forEach(s -> log.info(s));
            String status = output.printStatus();
            if (status.contains("SUCC")) {
                log.info(GREEN_BOLD + status + RESET);
            } else {
                log.info(RED_BOLD + status + RESET);
            }
        } else {
            keepTranslation = true;
            log.error(output.printErrors());
        }
    }

    private static void createCProverFolder(String fileName) {
        File f = new File(fileName);
        File dir = new File(f.getAbsolutePath() + File.separator + "org" + File.separator + "cprover");
        log.debug("Copying CProver.java to " + dir.getAbsolutePath());
        dir.mkdirs();
        try {
            InputStream is = CLI.class.getResourceAsStream("/cli/CProver.java");
            String content = convertStreamToString(is);
            File to = new File(dir.toPath() + File.separator + "CProver.java");
            Files.write(to.toPath(), content.getBytes());
        } catch (IOException e) {
            e.printStackTrace();
            throw new TranslationException("Error trying to copy CProver.java");
        }
    }

    static String convertStreamToString(java.io.InputStream is) {
        java.util.Scanner s = new java.util.Scanner(is).useDelimiter("\\A");
        return s.hasNext() ? s.next() : "";
    }

    public static void cleanUp() {
        if (!didCleanUp && !keepTranslation) {
            deleteFolder(tmpFolder, false);
            if (!keepTranslation) {
                try {
                    if (tmpFolder.exists()) {
                        Files.delete(tmpFolder.toPath());
                    }
                } catch (IOException e) {
                    //log.info("Could not delete tmp folder.");
                }
            }
        }
        didCleanUp = true;
    }

    public static void deleteFolder(File folder, boolean all) {
        File[] tmpFiles = folder.listFiles();
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
        }
    }

    static CompilationUnit rewriteAssert(CompilationUnit cu) {
        return Jml2JavaFacade.translate(cu);
    }

    private static boolean verifyJavaVersion(String binary) {
        String[] commands = new String[]{binary, "-version"};
        Process p = null;
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
    public void run() {
        if (debugMode) {
            Configurator.setRootLevel(Level.DEBUG);
            keepTranslation = true;
        }
        if (forceInlining) {
            forceInliningLoops = true;
            forceInliningMethods = true;
        }
        translateAndRunJBMC(fileName);
        if (doSanityCheck) {
            doSanityCheck = false;
            translateAndRunJBMC(fileName);
        }
        System.exit(0);
    }

}


