package jjbmc;

import lombok.Data;
import org.jspecify.annotations.Nullable;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

import static jjbmc.ErrorLogger.info;
import static picocli.CommandLine.*;


/**
 * Created by jklamroth on 1/15/19.
 */

@Command(name = "openJBMC", header = "@|bold openJBMC Bounded Model checking for JML|@")
@Data
public class JJBMCOptions {
    public static final int jbmcMajorVer = 5;
    public static final int jbmcMinorVer = 22;

    public List<String> apiArgs = new ArrayList<>(10);

    @Option(names = {"-kt", "-keepTranslation"},
            description = "Keep the temporary file which contains the translation of the given file.")
    public boolean keepTranslation = false;

    @Option(names = {"-fi", "-forceInlining"},
            description = "Inline methods and unroll loops even if a contract is available")
    public boolean forceInlining;
    @Option(names = {"-fil", "-forceInliningLoopsOnly"},
            description = "Unroll loops even if a loop contract is available")
    public boolean forceInliningLoops;

    @Option(names = {"-fim", "-forceInliningMethodsOnly"},
            description = "Inline methods even if a method contract is available")
    public boolean forceInliningMethods;

    @Option(names = {"-c", "-clock"},
            description = "Print out timing information.")
    public boolean timed;

    @Option(names = {"-dsa", "-dontsplitasserts"},
            description = "Split assertions if possible.")
    public boolean splitAssertions = true;

    @Option(names = {"-t", "-timeout"},
            description = "Provide a timeout in ms for each jbmc call. (default 10s)",
            arity = "0..1")
    public int timeout = 10000;

    @Parameters(index = "1", arity = "0..1", description = "The method to be verified. If not provided -va is automatically added.")
    @Nullable
    public String functionName = null;

    @Option(names = {"-tr", "-trace"},
            description = "Prints out traces for failing pvcs.")
    public boolean runWithTrace = false;

    @Option(names = {"-jbmc", "-jbmcBinary"},
            description = "allows to set the jbmc binary that is used for the verification (has to be relative or absolute path no alias)")
    public String jbmcBin = "jbmc";

    @Option(names = {"-lf", "--libFiles"},
            description = "Files to be copied to the translation folder.")
    public String[] libFiles = new String[]{};

    @Option(names = {"-jc", "-javac"},
            description = "allows to set the javac binary that is used for compilation of source files manually")
    public String javacBin = "javac";

    @Option(names = {"-ci", "-contractIndex"},
            description = "Allows to specify which of the contracts is going to be specified index from 0 upwards",
            arity = "0..1")
    private int caseIdx = 0;

    @Option(names = {"-mas", "-maxArraySize"},
            description = "Sets the maximum size more nondeterministic arrays.",
            arity = "0..1")
    private int maxArraySize = -1;

    @Option(names = {"-sc", "-sanityCheck"},
            description = "Adds a check for each method if assumptions are equals to false.",
            arity = "0..1")
    public boolean doSanityCheck = false;

    @Option(names = {"-d", "-debug"},
            description = "Runs JJBMC in debug mode. More outputs and preventing clean up of temporary files.")
    private boolean debugMode = false;

    @Parameters(index = "0", arity = "1", description = "The file containing methods to be verified.")
    private Path fileName;
    @Option(names = {"-u", "-unwind"},
            description = "Number of times loops are unwound. (default 5)",
            arity = "0..1")
    private int unwinds = -1;

    @Option(names = {"-j", "-jbmcOptions"}, description = "Options to be passed to jbmc.")
    private List<String> jbmcOptions = new ArrayList<>();

    @Option(names = {"-h", "-help"}, usageHelp = true,
            description = "Print usage help and exit.")
    private boolean usageHelpRequested;

    @Option(names = {"-rv", "-relevantVar"},
            description = "Names of variables whos values should be printed in a trace. (Has to be run with -tr option)")
    private List<String> relevantVars = new ArrayList<>();

    @Option(names = {"-ft", "-fullTrace"}, description = "Prevents traces from being filtered for relevant variables and prints all values. " +
            "(Has to be run with -tr option)")
    private boolean fullTraceRequested = false;

    @Option(names = {"-pp", "-proofPreconditions"}, description = "Adds additional assertions proving the preconditions " +
            "of called methods while still inlining them. (implies -fim option)")
    public boolean proofPreconditions = false;
    private @Nullable Path tmpFolder;
    private @Nullable Path tmpFile;

    private final boolean isWindows = System.getProperty("os.name")
            .toLowerCase().startsWith("windows");
    private Map<String, String> expressionMap = new HashMap<>();


    public void reset() {
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

    public Path getTmpFile() {
        if (tmpFile == null) {
            var p = getTmpFolder().resolve(fileName.getFileName());
            setTmpFile(p);
            return p;
        }
        return tmpFile;
    }

    public Path getTmpFolder() {
        if (tmpFolder == null) {
            var p = fileName.resolveSibling("tmp");
            setTmpFolder(p);
            return p;
        }
        return tmpFolder;
    }

    public int getUnwinds() {
        if (unwinds < 0) {
            info("No unwind argument found. Default to 7.");
            unwinds = 7;
        }
        return unwinds;
    }


    public int getMaxArraySize() {
        if (maxArraySize < 0) {
            info("No maxArraySize argument found. Default to " + (unwinds - 2) + ".");
            setMaxArraySize(Math.max(unwinds - 2, 0));
        }
        return maxArraySize;
    }

    public Path getJavacBinary() {
        return Objects.requireNonNull(getPath(javacBin), "Could not find javac on $PATH");
    }

    private @Nullable Path getPath(String fileName) {
        return Arrays.stream(System.getenv("PATH").split(File.pathSeparator))
                .map(it -> Paths.get(it, fileName))
                //.peek(System.out::println)
                .filter(Files::exists)
                .findFirst()
                .map(Path::toAbsolutePath)
                .orElse(null);
    }

    public Path getJbmcBinary() {
        return Objects.requireNonNull(getPath(jbmcBin), "Could not find jbmc on $PATH");
    }
}
