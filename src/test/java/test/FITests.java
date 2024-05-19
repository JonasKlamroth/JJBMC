package test;

import jjbmc.JBMCOptions;
import jjbmc.CostumPrintStream;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Order;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import jjbmc.FunctionNameVisitor.TestBehaviour;
import utils.Utils;

import java.io.IOException;
import java.util.stream.Stream;

@Order(value = 2)
//@Execution(ExecutionMode.CONCURRENT)
public class FITests {

    @BeforeAll
    public static void init() {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
        JBMCOptions.forceInliningMethods = true;
    }

    @AfterEach
    public void after() {
        JBMCOptions.cleanUp();
    }


    @AfterAll
    public static void setBack() {
        JBMCOptions.forceInliningMethods = false;
    }

    public static Stream<Arguments> getParameters() throws IOException {
        init();
        return Utils.prepareParameters(Utils.SRC_TEST_JAVA.resolve("tests").resolve("FITests.java"));
    }

    @ParameterizedTest
    @MethodSource("getParameters")
    public void runTestSuite(String classFile, String function, int unwind, TestBehaviour behaviour,
                             String parentFolder) throws IOException, InterruptedException {
        Utils.runTests(classFile, function, unwind, behaviour, parentFolder);
    }

}
