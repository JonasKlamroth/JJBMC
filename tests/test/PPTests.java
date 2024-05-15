package test;

import cli.CLI;
import cli.CostumPrintStream;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Order;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import utils.TestBehaviour;
import utils.Utils;

import java.io.File;
import java.io.IOException;
import java.util.stream.Stream;

@Order(value = 3)
public class PPTests {

    @BeforeAll
    public static void init() {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
        CLI.proofPreconditions = true;
    }

    @AfterEach
    public void after() {
        CLI.cleanUp();
    }

    @AfterAll
    public static void setBack() {
        CLI.proofPreconditions = false;
    }

    public static Stream<Arguments> getParameters() {
        return Utils.prepareParameters(Utils.baseTestFolder + "tests" + File.separator + "PPTests.java");
    }

    @ParameterizedTest
    @MethodSource("getParameters")
    public void runTestSuite(String classFile, String function, int unwind, TestBehaviour behaviour,
                             String parentFolder) throws IOException, InterruptedException {
        Utils.runTests(classFile, function, unwind, behaviour, parentFolder);
    }

}
