package jjbmc;

import picocli.CommandLine;

/**
 * The entry point for the program. Initializing piccoli cli and setting costum print streams
 *
 * @author jklamroth
 * @version 1 (1.10.18)
 */
public class Main {
    public static void main(String[] args) throws Exception {
        JBMCOptions cli = new JBMCOptions();
        CommandLine cmd = new CommandLine(cli)
                .setCaseInsensitiveEnumValuesAllowed(true)
                .setColorScheme(CommandLine.Help.defaultColorScheme(CommandLine.Help.Ansi.AUTO));
        cmd.parseArgs(args);
        Operations ops = new Operations(cli);
        ops.call()
    }
}