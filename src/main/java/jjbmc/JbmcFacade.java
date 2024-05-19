package jjbmc;


import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static jjbmc.ErrorLogger.*;

public class JbmcFacade {
    static boolean verifyJBMCVersion(String jbmcBin, boolean isWindows) {
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
                sb.append(System.lineSeparator());
                line = stdInput.readLine();
            }

            String sb2 = "";
            String line2 = stdInput.readLine();
            while (line2 != null) {
                sb.append(line);
                sb.append(System.lineSeparator());
                line = stdError.readLine();
            }

            //Has to stay down here otherwise not reading the output may block the process
            process.waitFor();

            String output = sb.toString();
            String error = sb2;
            if (output.toLowerCase().contains("jbmc version")) {
                debug("Found valid jbmc version: " + output);
                Pattern pattern = Pattern.compile("jbmc version (\\d*)\\.(\\d*)\\.(\\d*)? \\(", Pattern.CASE_INSENSITIVE);
                Matcher matcher = pattern.matcher(output);
                boolean matchFound = matcher.find();
                if (Integer.parseInt(matcher.group(1)) < JBMCOptions.jbmcMajorVer) {
                    error("Error validating jbmc binary \"" + jbmcBin + "\"");
                    error("Found version: " + output);
                    error("but at least version " + JBMCOptions.jbmcMajorVer + "." + JBMCOptions.jbmcMinorVer + " is required.");
                    error("Either install jbmc and make sure it is included in the path or provide " +
                            "a jbmc binary manually with the -jbmcBinary option");
                    error("To install jbmc (as part of cbmc) head to https://github.com/diffblue/cbmc/releases/ ");
                    return false;
                } else if (Integer.parseInt(matcher.group(2)) < JBMCOptions.jbmcMinorVer) {
                    error("Error validating jbmc binary \"" + jbmcBin + "\"");
                    error("Found version: " + output);
                    error("but at least version " + JBMCOptions.jbmcMajorVer + "." + JBMCOptions.jbmcMinorVer + " is required.");
                    error("Either install jbmc and make sure it is included in the path or provide " +
                            "a jbmc binary manually with the -jbmcBinary option");
                    error("To install jbmc (as part of cbmc) head to https://github.com/diffblue/cbmc/releases/ ");
                    return false;
                }
                return true;
            }
        } catch (IOException | InterruptedException e) {
            error("Error validating jbmc binary \"" + jbmcBin + "\" (" + e.getMessage() + ")");
            error("Either install jbmc and make sure it is included in the path or provide a jbmc binary manually with the -jbmcBinary option");
            error("To install jbmc (as part of cbmc) head to https://github.com/diffblue/cbmc/releases/ ");
            //e.printStackTrace();
            return false;
        }
        error("Error validating jbmc binary \"" + jbmcBin + "\"");
        error("Either install jbmc and make sure it is included in the path or provide a jbmc binary manually with the -jbmcBinary option");
        error("To install jbmc (as part of cbmc) head to https://github.com/diffblue/cbmc/releases/ ");
        return true;
    }
}
