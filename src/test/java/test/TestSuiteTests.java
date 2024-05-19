package test;

import jjbmc.JBMCOptions;
import org.junit.jupiter.api.*;
import jjbmc.FunctionNameVisitor.TestBehaviour;
import utils.Utils;

import java.io.IOException;
import java.util.stream.Stream;

public class TestSuiteTests {
    @TestFactory
    public Stream<DynamicTest> runTestSuite(String classFile, String function, int unwind, TestBehaviour behaviour,
                                            String parentFolder) throws IOException {
        return Utils.prepareParameters(Utils.SRC_TEST_JAVA.resolve("tests").resolve("TestSuite.java"))
                .map((it) -> DynamicTest.dynamicTest(
                        it.toString(),
                        () -> {
                            Utils.runTests(classFile, function, unwind, behaviour, parentFolder);
                            JBMCOptions.cleanUp();
                        }
                ));
    }
}
