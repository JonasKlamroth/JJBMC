package test;

import org.junit.jupiter.api.Order;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import jjbmc.FunctionNameVisitor.TestBehaviour;
import utils.Utils;

import java.io.IOException;
import java.util.stream.Stream;

@Order(value = 1)
public class AssignableTests {
    public static Stream<Arguments> assignableParameter() throws IOException {
        return Utils.prepareParameters(Utils.SRC_TEST_JAVA.resolve("tests").resolve("AssignableTests.java"));
    }

    @ParameterizedTest
    @MethodSource("assignableParameter")
    public void runAssignableTests(String classFile, String function, int unwind, TestBehaviour behaviour, String parentFolder) throws IOException, InterruptedException {
        Utils.runTests(classFile, function, unwind, behaviour, parentFolder);
    }


}
