import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.*;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import picocli.CommandLine;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintStream;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Arrays;

import static com.sun.org.apache.bcel.internal.util.SecuritySupport.getResourceAsStream;


/**
 * @author jklamroth
 * @version 1 (1.10.18)
 */
public class Main {


    public static final void main(String[] args) throws Exception {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
        CommandLine.run(new CLI(), args);
        //cleanUp();
    }

    /*
    This only prevents some error messages to be displayed.
     */
    static class CostumPrintStream extends PrintStream {
        static private boolean filtered = false;

        public CostumPrintStream(OutputStream out) {
            super(out);
        }

        @Override
        public void print(String s) {
            if(!s.startsWith("class ")) {
                super.print(s);
            } else {
                filtered = true;
            }
        }

        @Override
        public void write(byte[] buf, int off, int len) {
            if(!filtered) {
                super.write(buf, off, len);
            } else {
                filtered = false;
            }
        }
    }
}