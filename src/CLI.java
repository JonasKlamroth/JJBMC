import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.Factory;
import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

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
        File tmpFile;
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
            System.arraycopy(apiArgs, 0, commands, 2, apiArgs.length);
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


        } catch (IOException | InterruptedException e) {
            System.out.println("Error during preparation.");
            e.printStackTrace();
        }
        //cleanUp();
        System.out.println("Complilation sucessfull.");
        return tmpFile;
    }

    static public void translateAndRunJBMC() {
        File tmpFile = prepareForJBMC();
        if(tmpFile == null) {
            System.out.println("Error preparing translation.");
            return;
        }
        System.out.println("Parse function names.");
        FunctionNameVisitor.parseFile(fileName);
        List<String> functionNames = FunctionNameVisitor.getFunctionNames();
        List<String> allFunctionNames = new ArrayList<>(functionNames);
        if(functionName != null) {
            functionNames = functionNames.stream().filter(f -> f.contains("." + functionName)).collect(Collectors.toList());
            if(functionNames.size() == 0) {
                System.out.println("Function " + functionName + " could not be found in the specified file.");
                System.out.println("Found the following functions: " + allFunctionNames.toString());
                return;
            }
        }
        System.out.println("Run jbmc for " +functionNames.size() + " functions.");
        int NTHREADS = 4;
        ExecutorService executerService = Executors.newFixedThreadPool(NTHREADS);
        for(String functionName : functionNames) {
            //functionName = tmpFile.getName().replace(".java", "") + "." + functionName;
            Runnable worker = new Runnable() {
                @Override
                public void run() {
                    runJBMC(tmpFile, functionName);
                }
            };
            //runJBMC(tmpFile, functionName);
            executerService.execute(worker);
        }
        executerService.shutdown();
        try {
            executerService.awaitTermination(10000, TimeUnit.SECONDS);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    static private List<String> prepareJBMCOptions(List<String> options) {
        List<String> res = new ArrayList<>();
        for(String s : options) {
            res.addAll(Arrays.asList(s.split(" ")));
        }
        return res;
    }

    static public void runJBMC(File tmpFile, String functionName) {
        try {
            String out  = "Running jbmc for function: " + functionName;
            //commands = new String[] {"jbmc", tmpFile.getAbsolutePath().replace(".java", ".class")};
            String classFile = tmpFile.getName().replace(".java", ".class");

            ArrayList<String> tmp = new ArrayList<>();
            tmp.add("./jbmc");
            tmp.add(classFile);
            tmp.add("--function");
            tmp.add(functionName);
            jbmcOptions = prepareJBMCOptions(jbmcOptions);
            tmp.addAll(jbmcOptions);
            tmp.add("--xml-ui");
            //tmp.add("--cp");
            String libPath = System.getProperty("java.library.path");
            //tmp.add(libPath);
            String[] commands = new String[tmp.size()];
            commands = tmp.toArray(commands);

            System.out.println(out + "\n" + Arrays.toString( commands ));
            Runtime rt = Runtime.getRuntime();
            rt.addShutdownHook(new Thread(CLI::cleanUp));
            Process proc = rt.exec(commands, null, tmpFolder);

            BufferedReader stdInput = new BufferedReader(new
                    InputStreamReader(proc.getInputStream()));

            BufferedReader stdError = new BufferedReader(new
                    InputStreamReader(proc.getErrorStream()));



            StringBuilder sb = new StringBuilder();
            String line = stdInput.readLine();
            while (line != null) {
                sb.append(line);
                sb.append(System.getProperty("line.separator"));
                line = stdInput.readLine();
            }
            StringBuilder esb = new StringBuilder();
            String eline = stdError.readLine();
            while (eline != null) {
                esb.append(eline);
                esb.append(System.getProperty("line.separator"));
                eline = stdError.readLine();
            }

            //Has to stay down here otherwise not reading the output may block the process
            proc.waitFor();

            String xmlOutput = sb.toString();
            JBMCOutput output = XmlParser.parse(xmlOutput, tmpFile);
            if(output == null) {
                throw new RuntimeException("Error parsing xml-output of JBMC.");
            }
            out = "Result for function " + functionName + ":";
            if(output.errors.size() == 0) {
                out += output.printAllTraces() + "\n";
                out += output.printStatus() + "\n";
            } else {
                out += output.printErrors() + "\n";
            }

            if(proc.exitValue() != 0 && proc.exitValue() != 10) {
                out += "JBMC did not terminate as expected." + "\n";
            } else {
                out += "JBMC terminated normally." + "\n";
            }
            System.out.println(out);

       } catch (Exception e) {
            System.out.println("Error running jbmc.");
            e.printStackTrace();
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
            rt.addShutdownHook(new Thread(CLI::cleanUp));
            Process proc = rt.exec(commandsChmod);
            proc.waitFor();
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
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
      //  if(!didCleanUp) {
      //      deleteFolder(tmpFolder);
      //      if (!keepTranslation) {
      //          try {
      //              if (tmpFolder.exists()) {
      //                  Files.delete(tmpFolder.toPath());
      //              }
      //          } catch (IOException e) {
      //              //System.out.println("Could not delete tmp folder.");
      //          }
      //      }
      //  }
        didCleanUp = true;
    }

    public static void deleteFolder(File folder) {
        File[] tmpFiles = folder.listFiles();
        assert tmpFiles != null;
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


