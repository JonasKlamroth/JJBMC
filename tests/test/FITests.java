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
import translation.FunctionNameVisitor;
import utils.TestBehaviour;
import utils.Utils;

import java.io.File;
import java.io.IOException;
import java.util.stream.Stream;

@Order(value = 2)
//@Execution(ExecutionMode.CONCURRENT)
public class FITests {

    @BeforeAll
    public static void init() {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
        CLI.forceInliningMethods = true;
    }

    @AfterEach
    public void after() {
        CLI.cleanUp();
    }


    @AfterAll
    public static void setBack() {
        CLI.forceInliningMethods = false;
    }

    public static Stream<Arguments> getParameters() {
        init();
        return Utils.prepareParameters(Utils.baseTestFolder + "tests" + File.separator + "FITests.java");
    }

    @ParameterizedTest
    @MethodSource("getParameters")
    public void runTestSuite(String classFile, String function, String unwind, TestBehaviour behaviour,
                             String parentFolder) throws IOException, InterruptedException {
        Utils.runTests(classFile, function, unwind, behaviour, parentFolder);
    }

}
