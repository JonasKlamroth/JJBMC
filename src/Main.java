import picocli.CommandLine;

import java.util.function.Function;

/**
 * @author jklamroth
 * @version 1 (1.10.18)
 */
public class Main {


    public static final void main(String[] args) throws Exception {
        if(!(System.err instanceof CostumPrintStream)) {
            System.setErr(new CostumPrintStream(System.err));
            System.setOut(new CostumPrintStream(System.out));
        }
        CLI.reset();
        CommandLine.run(new CLI(), args);
    }
}