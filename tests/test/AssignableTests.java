package test;

import cli.CLI;
import cli.CostumPrintStream;
import java.io.File;
import java.io.IOException;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Order;
import translation.FunctionNameVisitor;
import utils.Utils;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.*;
import java.util.stream.Stream;

@Order(value = 1)
//@Execution(ExecutionMode.CONCURRENT)
public class AssignableTests {

    @BeforeAll
    public static void init() {
    //    System.setErr(new CostumPrintStream(System.err));
    //    System.setOut(new CostumPrintStream(System.out));
    }

    @AfterEach
    public void after() {
        CLI.cleanUp();
    }

    public static Stream<Arguments> assignableParameter() {
        init();
        return Utils.prepareParameters(Utils.baseTestFolder + "tests" + File.separator + "AssignableTests.java");
    }

    @ParameterizedTest
    @MethodSource("assignableParameter")
    public void runAssignableTests(String classFile, String function, String unwind,
                                   FunctionNameVisitor.TestBehaviour behaviour,
                                   String parentFolder) throws IOException, InterruptedException {
        Utils.runTests(classFile, function, unwind, behaviour, parentFolder);
    }


}
