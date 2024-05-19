package test;

import cli.CLI;
import cli.CostumPrintStream;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Order;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import translation.FunctionNameVisitor;
import utils.Utils;

import java.io.File;
import java.io.IOException;
import java.util.stream.Stream;

@Order(value = 2)
//@Execution(ExecutionMode.CONCURRENT)
public class Assignable2Tests {

    @BeforeAll
    public static void init() {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
    }

    @AfterEach
    public void after() {
        CLI.cleanUp();
    }

    public static Stream<Arguments> assignableParameter2() {
        init();
        return Utils.prepareParameters(Utils.baseTestFolder + "tests" + File.separator + "AssignableTests2.java");
    }

    @ParameterizedTest
    @MethodSource("assignableParameter2")
    public void runAssignableTests2(String classFile, String function, String unwind, FunctionNameVisitor.TestBehaviour behaviour,
                                    String parentFolder) throws IOException, InterruptedException {
        Utils.runTests(classFile, function, unwind, behaviour, parentFolder);
    }
}
