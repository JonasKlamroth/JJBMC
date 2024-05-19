package test;

import jjbmc.JBMCOptions;
import jjbmc.CostumPrintStream;
import jjbmc.FunctionNameVisitor;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;
import utils.Utils;

import java.io.IOException;
import java.util.stream.Stream;

public class Assignable2Tests {

    public static void init() {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
    }

    public void after() {
        JBMCOptions.cleanUp();
    }

    @TestFactory
    public Stream<DynamicTest> runAssignableTests2(String classFile, String function, int unwind, FunctionNameVisitor.TestBehaviour behaviour,
                                                   String parentFolder) throws IOException, InterruptedException {

        return Utils.prepareParameters(Utils.SRC_TEST_JAVA.resolve("tests").resolve("AssignableTests2.java"))
                .map(it -> DynamicTest.dynamicTest(it.toString(),
                        () -> {
                            Utils.runTests(classFile, function, unwind, behaviour, parentFolder);
                            after();
                        }));
    }
}
