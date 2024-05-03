package cli.javac;

import cli.CLI;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (03.05.24)
 */
public class JavacFacade {
    public static void compile(File tmpFile, File tmpFolder) throws IOException, InterruptedException {
        JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
        final var outputJavac = new File(tmpFolder, "compilationErrors.txt");

        if (compiler != null) {
            // use internal available compiler
            CLI.log.info("Internal compiler available {} and will be used", compiler.name());
            try (FileOutputStream out = new FileOutputStream(outputJavac)) {
                compiler.run(null, out, out, "-g", tmpFile.getAbsolutePath());
            } catch (IOException e) {
                e.printStackTrace();
            }
        } else {
            String javacPath = find(CLI.javacBin);
            CLI.log.info("Javac path is {}", javacPath);
            String[] javac = new String[]{javacPath, "-g", tmpFile.getAbsolutePath()};
            List<String> commands = Stream.concat(Arrays.stream(javac), Arrays.stream(CLI.apiArgs)).toList();
            CLI.log.debug("Compiling translated file: {}", commands);
            ProcessBuilder pb = new ProcessBuilder().command(commands)
                    .redirectOutput(outputJavac)
                    .redirectErrorStream(true)
                    .directory(tmpFolder);
            Process proc = pb.start();
            proc.waitFor();

            if (proc.exitValue() != 0) {
                CLI.keepTranslation = true;
                CLI.log.error("Compilation failed. See compilationErrors.txt for javac output.");
            }
        }
    }

    private static String find(String javacBin) {
        Path p = Paths.get(javacBin);
        if (p.isAbsolute())
            return p.toAbsolutePath().toString();
        String[] paths = System.getenv("PATH").split("" + File.pathSeparatorChar);
        for (String path : paths) {
            Path candidate = Paths.get(path, javacBin);
            if (Files.isExecutable(candidate)) {
                return candidate.toAbsolutePath().toString();
            }
        }
        return javacBin;
    }
}
