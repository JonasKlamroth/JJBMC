package traceTest;

import cli.CLI;
import cli.CostumPrintStream;
import cli.JBMCOutput;
import cli.TraceParser;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.parallel.Execution;
import org.junit.jupiter.api.parallel.ExecutionMode;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;


@Execution(ExecutionMode.SAME_THREAD)
public class TraceTests {

    @BeforeAll
    public static void init() {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
    }

    @AfterEach
    public void after() {
        CLI.cleanUp();
    }

    public static Stream<Arguments> getParameters() {
        List<Arguments> params = new ArrayList<>();
        params.add(Arguments.of("./testRes/traceTest/TraceTestCases.java",
                "./testRes/traceTest/TmpTestOut.txt",
                new ArrayList<>(Arrays.asList("k", "tt", "table")),
                "test"));
        params.add(Arguments.of("./testRes/traceTest/TraceTestCases.java",
                "./testRes/traceTest/TmpTestOut2.txt",
                new ArrayList<>(),
                "test2"));
        params.add(Arguments.of("./testRes/traceTest/TraceTestCases.java",
                "./testRes/traceTest/TmpTestOut3.txt",
                new ArrayList<>(List.of("iotable")),
                "test3"));
        params.add(Arguments.of("./testRes/traceTest/TraceTestCases.java",
                "./testRes/traceTest/TmpTestOut4.txt",
                new ArrayList<>(),
                "test4"));
        params.add(Arguments.of("./testRes/traceTest/TraceTestCases.java",
                "./testRes/traceTest/TmpTestOut5.txt",
                new ArrayList<>(),
                "test5"));
        params.add(Arguments.of("./testRes/traceTest/TraceTestCases.java",
                "./testRes/traceTest/TmpTestOut6.txt",
                new ArrayList<>(),
                "test6"));

        return params.stream();
    }

    @ParameterizedTest
    @MethodSource("getParameters")
    public void traceTest(String inputFile, String outFile, ArrayList<String> relevantVars, String functionName) {
        CLI.reset();
        CLI.runWithTrace = true;
        CLI.keepTranslation = true;
        CLI.functionName = functionName;
        CLI.relevantVars.addAll(relevantVars);
        CLI.translateAndRunJBMC(inputFile);
        int idx = inputFile.lastIndexOf(File.separator);
        String path = inputFile.substring(0, idx) + "/tmp/xmlout.xml";
        File f = new File(path);
        assertTrue(f.exists());
        JBMCOutput output = TraceParser.parse(f, true);
        String traces = output.printAllTraces();
        String[] traceSplits = traces.split("\n");
        List<String> assignments = new ArrayList<>();
        for (String s : traceSplits) {
            if (s.startsWith("in line")) {
                assignments.add(s);
            }
        }
        File reference = new File(outFile);

        assertTrue(reference.exists());
        try {
            List<String> lines = Files.readAllLines(reference.toPath());
            assertEquals(lines.size(), assignments.size());
            for (int i = 0; i < lines.size(); ++i) {
                assertEquals(lines.get(i).trim(), assignments.get(i).trim());
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

    }

}