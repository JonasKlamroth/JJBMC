package jjbmc.trace;

import jjbmc.JBMCOutput;
import jjbmc.JJBMCOptions;
import jjbmc.Operations;
import org.junit.jupiter.api.parallel.Execution;
import org.junit.jupiter.api.parallel.ExecutionMode;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.xml.sax.SAXException;

import javax.xml.parsers.ParserConfigurationException;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;


@Execution(ExecutionMode.SAME_THREAD)
public class TraceTests {
    public static Stream<Arguments> getParameters() {
        return Stream.of(
                Arguments.of("src/test/resources/traceTest/TraceTestCases.java",
                        "src/test/resources/traceTest/TmpTestOut.txt",
                        List.of("k", "tt", "table"),
                        "test"),
                Arguments.of("src/test/resources/traceTest/TraceTestCases.java",
                        "src/test/resources/traceTest/TmpTestOut2.txt",
                        List.of(),
                        "test2"),
                Arguments.of("src/test/resources/traceTest/TraceTestCases.java",
                        "src/test/resources/traceTest/TmpTestOut3.txt",
                        List.of("iotable"),
                        "test3"),
                Arguments.of("src/test/resources/traceTest/TraceTestCases.java",
                        "src/test/resources/traceTest/TmpTestOut4.txt",
                        List.of(),
                        "test4"),
                Arguments.of("src/test/resources/traceTest/TraceTestCases.java",
                        "src/test/resources/traceTest/TmpTestOut5.txt",
                        List.of(),
                        "test5"),
                Arguments.of("src/test/resources/traceTest/TraceTestCases.java",
                        "src/test/resources/traceTest/TmpTestOut6.txt",
                        List.of(),
                        "test6"));
    }

    @ParameterizedTest
    @MethodSource("getParameters")
    public void traceTest(Path inputFile, String outFile, List<String> relevantVars, String functionName) throws Exception {

        JJBMCOptions options = new JJBMCOptions();
        options.reset();
        options.runWithTrace = true;
        options.keepTranslation = true;
        options.functionName = functionName;
        options.getRelevantVars().addAll(relevantVars);
        options.setTmpFile(Paths.get("tmp"));

        Operations operations = new Operations(options);
        operations.translateAndRunJBMC(inputFile);

        var f = inputFile.getParent().resolve("tmp/xmlout.xml").toFile();
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