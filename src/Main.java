import picocli.CommandLine;

/**
 * @author jklamroth
 * @version 1 (1.10.18)
 */
public class Main {


    public static final void main(String[] args) throws Exception {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
        CommandLine.run(new CLI(), args);
    }
}