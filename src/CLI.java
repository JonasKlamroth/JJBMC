import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.Factory;
import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
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

    @Option(names = {"-kt", "-keepTranslation"}, description = "Keep the temporary file which contains the translation of the given file.")
    static boolean keepTranslation = false;

    @Option(names = {"-va", "-verifyAll"}, description = "Verify all functions not just one.")
    static boolean verifyAll = false;

    @Parameters(index="0", arity = "1", description = "The file containing methods to be verified.")
    static String fileName = null;

    @Parameters(index="1", arity = "0..1", description = "The method to be verified. If not provided -va is automatically added.")
    static String functionName = null;

    @Option(names = {"-df", "-dontFilter"}, description = "If set all JBMC output is printed.")
    static boolean filterOutput = true;

    @Option(names = {"-j", "-jbmcOptions"}, description = "Options to be passed to jbmc.")
    static List<String> jbmcOptions = new ArrayList<>();

    @Option(names = {"-h", "-help"}, usageHelp = true,
            description = "Print usage help and exit.")
    static boolean usageHelpRequested;

    static File tmpFolder = null;
    private static boolean didCleanUp = false;

    @Override
    public void run() {
        translateAndRunJBMC();
    }

    public static String translate(File file) throws Exception {
        String[] args = {file.getAbsolutePath()};
        return translate(args);
    }

    public static String translate(File file, String[] apiArgs) throws Exception {
        String[] args = {file.getAbsolutePath()};
        return translate(args, apiArgs);
    }

    public static String translate(String[] args) throws Exception {
        return translate(args, new String[]{});
    }

    public static String translate(String[] args, String[] apiArgs) throws Exception {

        IAPI api = Factory.makeAPI(apiArgs);
        java.util.List<JmlTree.JmlCompilationUnit> cu = api.parseFiles(args);
        int a = api.typecheck(cu);
        if(a > 0) {
            System.out.println("OpenJml parser Error.");
            return null;
        }
        Context ctx = api.context();


        for (JmlTree.JmlCompilationUnit it : cu) {
            //System.out.println(api.prettyPrint(rewriteRAC(it, ctx)));
            JCTree t = rewriteAssert(it, ctx);
            return api.prettyPrint(t);
        }
        return null;
    }

    public static void translateAndRunJBMC(String file) {
        fileName = file;
        translateAndRunJBMC();
    }

    public static void translateAndRunJBMC(String file, String functionName) {
        CLI.functionName = functionName;
        fileName = file;
        translateAndRunJBMC();
    }

    public static File prepareForJBMC(String file, String[] apiArgs) {
        fileName = file;
        return prepareForJBMC(apiArgs);
    }

    public static File prepareForJBMC(String file) {
        fileName = file;
        return prepareForJBMC();
    }

    public static File prepareForJBMC() {
        File f = new File(fileName);
        return prepareForJBMC(new String[]{"-cp", new File(f.getParentFile(), "tmp").getAbsolutePath()});
    }

    public static File prepareForJBMC(String[] apiArgs) {
        File tmpFile = null;
        didCleanUp = false;
        try {
            File f = new File(fileName);
            if(!f.exists()) {
                System.out.println("Could not find file " + f);
                return null;
            }
            tmpFolder = new File(f.getParentFile(), "tmp");
            tmpFolder.mkdirs();
            tmpFile = new File(tmpFolder, f.getName());
            Files.copy(f.toPath(), tmpFile.toPath(), StandardCopyOption.REPLACE_EXISTING);

            String translation = translate(tmpFile, apiArgs);
            if(translation != null) {
                if (tmpFile.exists()) {
                    Files.delete(tmpFile.toPath());
                }
                Files.write(tmpFile.toPath(), translation.getBytes(), StandardOpenOption.CREATE);
                createCProverFolder(tmpFile.getAbsolutePath());
                if (!copyJBMC()) {
                    cleanUp();
                    return null;
                }
            } else {
                return null;
            }
        } catch (Exception e) {
            cleanUp();
            e.printStackTrace();
            return null;
        }

        try {
            Runtime rt = Runtime.getRuntime();

            String[] commands = new String[apiArgs.length + 2];
            commands[0] = "javac";
            commands[1] = tmpFile.getAbsolutePath();
            for(int i = 0; i < apiArgs.length; ++i) {
                commands[i + 2] = apiArgs[i];
            }
            System.out.println("Compiling translated file: " + Arrays.toString(commands));
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
                return null;
            }
            s = stdError.readLine();
            if (s != null) {
                System.out.println("Error compiling file: " + tmpFile.getPath());
                while (s != null) {
                    System.out.println(s);
                    s = stdError.readLine();
                }
                return null;
            }


        } catch (IOException e) {
            System.out.println("Error running JBMC.");
            e.printStackTrace();
        } catch (InterruptedException e) {
            System.out.println("Error. JBMC got interrupted.");
            e.printStackTrace();
        }
        //cleanUp();
        return tmpFile;
    }

    static public void translateAndRunJBMC() {
        File tmpFile = prepareForJBMC();
        List<String> functionNames = new ArrayList<>();
        functionNames.addAll(NameExctractionVisitor.parseFile(fileName));
        if(functionName != null) {
            functionNames = functionNames.stream().filter(f -> f.endsWith("." + functionName)).collect(Collectors.toList());
            if(functionNames.size() == 0) {
                System.out.println("Function " + functionName + " could not be found in the specified file.");
                return;
            }
        }
        for(String functionName : functionNames) {
            //functionName = tmpFile.getName().replace(".java", "") + "." + functionName;
            runJBMC(tmpFile, functionName);
        }
    }

    static private List<String> prepareJBMCOptions(List<String> options) {
        List<String> res = new ArrayList<>();
        for(String s : options) {
            for(String o : s.split(" "))
            res.add(o);
        }
        return res;
    }

    static public void runJBMC(File tmpFile, String functionName) {
        try {
            System.out.println("Running jbmc for function: " + functionName);
            //commands = new String[] {"jbmc", tmpFile.getAbsolutePath().replace(".java", ".class")};
            String classFile = tmpFile.getPath().replace(".java", ".class");

            ArrayList<String> tmp = new ArrayList<>();
            tmp.add(tmpFolder.getAbsolutePath() + File.separator + "jbmc");
            tmp.add(classFile);
            tmp.add("--function");
            tmp.add(functionName);
            jbmcOptions = prepareJBMCOptions(jbmcOptions);
            tmp.addAll(jbmcOptions);
            String[] commands = new String[tmp.size()];
            commands = tmp.toArray(commands);

            Runtime rt = Runtime.getRuntime();
            rt.addShutdownHook(new Thread(() -> {cleanUp();}));
            Process proc = rt.exec(commands);
            proc.waitFor();

            BufferedReader stdInput = new BufferedReader(new
                    InputStreamReader(proc.getInputStream()));

            BufferedReader stdError = new BufferedReader(new
                    InputStreamReader(proc.getErrorStream()));

            String s = stdInput.readLine();
            String out = "";
            String fullOut = "";
            if (s != null) {
                out += "JBMC Output" + (filterOutput ? " (filtered)" : "") + " for file: " + tmpFile.getPath().replace(".java", ".class") + " with function " + functionName + "\n";
                fullOut += "JBMC Output for file: " + tmpFile.getPath().replace(".java", ".class") + " with function " + functionName + "\n";
                while (s != null) {
                    if (!filterOutput || (s.contains("**") || s.contains("FAILURE") || s.contains("VERIFICATION"))) {
                        if(s.contains("FAILED")) {
                            out += RED_BOLD + s +  RESET + "\n";
                        } else if(s.contains("VERIFICATION")) {
                            out += GREEN_BOLD + s +  RESET + "\n";
                        } else {
                            out += s + "\n";
                        }
                    }
                    fullOut += s + "\n";
                    s = stdInput.readLine();
                }
                s = stdError.readLine();
                while (s != null) {
                    if (!filterOutput || (s.contains("**") || s.contains("FAILURE") || s.contains("VERIFICATION"))) {
                        out += s + "\n";
                    }
                    fullOut += s + "\n";
                    s = stdError.readLine();
                }
                if (!out.contains("VERIFICATION") && !out.contains("FAILURE")) {

                    System.out.println(fullOut);
                } else {
                    System.out.println(out);
                }
            }
        } catch (Exception e) {
            System.out.println("Error running jbmc.");
            e.printStackTrace();
            return;
        }
    }

    static private void createCProverFolder(String fileName) {
        File f = new File(fileName);
        File dir = new File(f.getParent() + File.separator + "org" + File.separator + "cprover");
        System.out.println("Copying CProver.java to " + dir.getAbsolutePath());
        dir.mkdirs();
        try {
            InputStream is = Main.class.getResourceAsStream("CProver.java");
            String content = convertStreamToString(is);
            File to = new File(dir.toPath() + File.separator + "CProver.java");
            Files.write(to.toPath(), content.getBytes());
        } catch (IOException e) {
            e.printStackTrace();
            throw new RuntimeException("Error trying to copy CProver.java");
        }
    }

    private static boolean copyJBMC() {
        try {
            InputStream is = Main.class.getResourceAsStream("jbmc");
            File to = new File(tmpFolder.getAbsolutePath() + File.separator + "jbmc");
            FileOutputStream buffer = new FileOutputStream(to.getAbsoluteFile());
            int nRead;
            byte[] data = new byte[1024];
            while ((nRead = is.read(data, 0, data.length)) != -1) {
                buffer.write(data, 0, nRead);
            }
            buffer.flush();
            buffer.close();
            is.close();

            ArrayList<String> tmp = new ArrayList<>();
            tmp.add("chmod");
            tmp.add("+x");
            tmp.add(tmpFolder.getAbsolutePath() + File.separator + "jbmc");
            String[] commandsChmod = new String[tmp.size()];
            commandsChmod = tmp.toArray(commandsChmod);

            Runtime rt = Runtime.getRuntime();
            rt.addShutdownHook(new Thread(() -> {cleanUp();}));
            Process proc = rt.exec(commandsChmod);
            proc.waitFor();
        } catch (IOException e) {
            System.out.println("Could not copy jbmc.");
            return false;
        } catch (InterruptedException e) {
            System.out.println("Could not copy jbmc.");
            return false;
        }
        return true;

    }

    static String convertStreamToString(java.io.InputStream is) {
        java.util.Scanner s = new java.util.Scanner(is).useDelimiter("\\A");
        return s.hasNext() ? s.next() : "";
    }

    public static void cleanUp() {
        if(!didCleanUp) {
            deleteFolder(tmpFolder);
            if (!keepTranslation) {
                try {
                    if (tmpFolder.exists()) {
                        Files.delete(tmpFolder.toPath());
                    }
                } catch (IOException e) {
                    //System.out.println("Could not delete tmp folder.");
                }
            }
        }
        didCleanUp = true;
    }

    public static void deleteFolder(File folder) {
        File[] tmpFiles = folder.listFiles();
        for(File f : tmpFiles) {
            if(!keepTranslation || !f.getName().endsWith(new File(fileName).getName())) {
                if (f.isDirectory()) {
                    deleteFolder(f);
                }
                try {
                    if(f.exists()) {
                        Files.delete(f.toPath());
                    }
                } catch (IOException ex) {
                    //System.out.println("Could not delete temporary file: " + f.getAbsolutePath());
                }
            }
        }
    }

    JCTree rewriteRAC(JmlTree.JmlCompilationUnit cu, Context context) {
        JmlAssertionAdder jaa = new JmlAssertionAdder(context, false, true);
        context.dump();
        return jaa.convert(cu);
    }

    static JCTree rewriteAssert(JmlTree.JmlCompilationUnit cu, Context context) {
        context.dump();
        return cu.accept(new BaseVisitor(context, JmlTree.Maker.instance(context)), null);
    }
}

class NameExctractionVisitor extends JmlTreeScanner {
    static private String packageName = "";
    static private List<String> functionNames = new ArrayList();
    static private String className = "";

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
        if(!f.contains("<init>")) {
            functionNames.add(f);
        }
        super.visitJmlMethodDecl(that);
    }

    public static List<String> parseFile(String fileName) {
        functionNames = new ArrayList();
        try {
            String[] args = {fileName};
            IAPI api = Factory.makeAPI();
            java.util.List<JmlTree.JmlCompilationUnit> cu = api.parseFiles(args);

            Context ctx = api.context();
            NameExctractionVisitor fnv = new NameExctractionVisitor();
            for (JmlTree.JmlCompilationUnit it : cu) {
                if(it.pid != null) {
                    packageName = it.pid.toString();
                }
                ctx.dump();
                it.accept(fnv);
            }
        } catch (Exception e) {
            System.out.println("error parsing for method names");
            e.printStackTrace();
        }
        return functionNames;
    }
}
