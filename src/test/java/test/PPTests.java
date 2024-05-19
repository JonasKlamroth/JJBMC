package test;

import jjbmc.JBMCOptions;
import jjbmc.FunctionNameVisitor.TestBehaviour;
import org.junit.jupiter.api.Order;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import utils.Utils;

import java.io.IOException;
import java.util.stream.Stream;

@Order(value = 3)
public class PPTests {
    public static Stream<Arguments> getParameters() throws IOException {
        return Utils.prepareParameters(Utils.SRC_TEST_JAVA.resolve("tests").resolve("PPTests.java"));
    }

    @ParameterizedTest
    @MethodSource("getParameters")
    public void runTestSuite(String classFile, String function, int unwind, TestBehaviour behaviour,
                             String parentFolder) throws IOException, InterruptedException {
        var cli = new JBMCOptions();
        JBMCOptions.proofPreconditions = true;
        Utils.runTests(classFile, function, unwind, behaviour, parentFolder);
        cli.cleanUp();
    }

}
