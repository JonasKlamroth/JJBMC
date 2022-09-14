package traceTest;

import cli.CLI;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import cli.CostumPrintStream;
import cli.JBMCOutput;
import cli.XmlParser2;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

@RunWith(Parameterized.class)
public class TraceTest {

    @Parameterized.Parameter(value = 0)
    public String inputFile;

    @Parameterized.Parameter(value = 1)
    public String outFile;

    @Parameterized.Parameter(value = 2)
    public List<String> relevantVars;

    @Parameterized.Parameter(value = 3)
    public String functionName;

    @BeforeClass
    public static void init() {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
    }
    @AfterClass
    public static void after() {
        CLI.cleanUp();
    }

    @Parameterized.Parameters
    public static Collection<Object[]> getParameters() {
        List<Object[]> params = new ArrayList<>();
        params.add(new Object[]{"." + File.separator + "testRes" + File.separator + "traceTest" + File.separator + "TmpTest.java",
                "." + File.separator + "testRes" + File.separator + "traceTest" + File.separator + "TmpTestOut.txt",
                new ArrayList<>(Arrays.asList(new String[]{"k", "tt", "table"})),
                "test"});
        params.add(new Object[]{"." + File.separator + "testRes" + File.separator + "traceTest" + File.separator + "TmpTest.java",
                "." + File.separator + "testRes" + File.separator + "traceTest" + File.separator + "TmpTestOut2.txt",
                new ArrayList<>(),
                "test2"});
        params.add(new Object[]{"." + File.separator + "testRes" + File.separator + "traceTest" + File.separator + "TmpTest.java",
                "." + File.separator + "testRes" + File.separator + "traceTest" + File.separator + "TmpTestOut3.txt",
                new ArrayList<>(Arrays.asList(new String[]{"iotable"})),
                "test3"});

        return params;
    }

    @Test
    public void traceTest() {
        Logger log = LogManager.getLogger(CLI.class);
        CLI.reset();
        CLI.runWithTrace = true;
        CLI.keepTranslation = true;
        CLI.functionName = this.functionName;
        CLI.relevantVars.addAll(relevantVars);
        CLI.translateAndRunJBMC(inputFile);
        int idx = inputFile.lastIndexOf(File.separator);
        String path = inputFile.substring(0, idx) + File.separator + "tmp" + File.separator + "xmlout.xml";
        File f = new File(path) ;
        assertTrue(f.exists());
        JBMCOutput output = XmlParser2.parse(f, true);
        String traces = output.printAllTraces();
        String[] traceSplits = traces.split("\n");
        List<String> assignments = new ArrayList<>();
        for(String s : traceSplits) {
            if(s.startsWith("in line")) {
                assignments.add(s);
            }
        }
        File reference = new File(outFile);
        assertTrue("Outfile " + outFile + " does not exist.", reference.exists());
        try {
            List<String> lines = Files.readAllLines(reference.toPath());
            assertEquals(lines.size(), assignments.size());
            for(int i = 0; i < lines.size(); ++i) {
                assertEquals(lines.get(i).trim(), assignments.get(i).trim());
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

    }

}