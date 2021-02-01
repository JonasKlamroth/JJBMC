import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;


import static org.junit.Assert.*;

public class XmlTest {

    public void runXmlTest(String xmlOutFile, String sourceFile, String outFile, Map<String, List<String>> paramMap, String functionName) throws IOException {
        List<String> allLines = Files.readAllLines(new File(xmlOutFile).toPath());
        String xmlString = String.join("\n", allLines);
        JBMCOutput out = XmlParser.parse(xmlString, new File(sourceFile), paramMap);
        String outString = printOutput(out, functionName);
        allLines = Files.readAllLines(new File(outFile).toPath());
        String referenceString = String.join("\n", allLines);

        assertEquals(referenceString, outString);
    }

    @Test
    public void test1() throws IOException {
        Map<String, List<String>> paramMap = new HashMap<>();
        List<String> params1 = new ArrayList<>();
        params1.add("a");
        List<String> params2 = new ArrayList<>();
        params2.add("i0");
        paramMap.put("TmpTest.test", params1);
        paramMap.put("$static_TmpTest.test2", params2);
        runXmlTest("testRes/xmlTest/TmpTest.test.xml", "testRes/xmlTest/TmpTest.java", "testRes/xmlTest/TmpTest.test.out", paramMap, "TmpTest.test:([I)V");

    }

    @Test
    public void test2() throws IOException {
        Map<String, List<String>> paramMap = new HashMap<>();
        List<String> params1 = new ArrayList<>();
        params1.add("a");
        List<String> params2 = new ArrayList<>();
        params2.add("i0");
        paramMap.put("TmpTest.test", params1);
        paramMap.put("$static_TmpTest.test2", params2);
        runXmlTest("testRes/xmlTest/TmpTest.test2.xml", "testRes/xmlTest/TmpTest.java", "testRes/xmlTest/TmpTest.test2.out", paramMap, "TmpTest.test2:(I)V");
    }

    private String printOutput(JBMCOutput output, String functionName) {
        StringBuilder sb = new StringBuilder();
        if(output == null) {
            throw new RuntimeException("Error parsing xml-output of JBMC.");
        }
        sb.append("Result for function " + functionName + ":\n");

        if(output.errors.size() == 0) {
                String traces = output.printAllTraces();
                if (!traces.isEmpty()) {
                    sb.append(traces);
                }
        } else {
            sb.append(output.printErrors());
        }
        return sb.toString();
    }
}
