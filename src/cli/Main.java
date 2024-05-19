package cli;

import picocli.CommandLine;

/**
 * The entry point for the program. Initializing piccoli cli and setting costum print streams
 *
 * @author jklamroth
 * @version 1 (1.10.18)
 */
public class Main {
    public static void main(String[] args) throws Exception {
        if (!(System.err instanceof CostumPrintStream)) {
            System.setErr(new CostumPrintStream(System.err));
            System.setOut(new CostumPrintStream(System.out));
        }
        CLI.reset();
        CommandLine cmd = new CommandLine(new CLI());
        cmd.execute(args);
    }
}