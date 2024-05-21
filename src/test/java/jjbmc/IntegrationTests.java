package jjbmc;

import jjbmc.utils.Utils;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Order;
import org.junit.jupiter.api.TestFactory;

import java.util.function.Consumer;
import java.util.stream.Stream;

@Order(value = 1)
public class IntegrationTests {
    @TestFactory
    public Stream<DynamicTest> assignableTests() throws Exception {
        return getTestStream("AssignableTests.java");
    }

    @TestFactory
    public Stream<DynamicTest> assignableTests2() throws Exception {
        return getTestStream("AssignableTests2.java");
    }

    @TestFactory
    public Stream<DynamicTest> fiTests() throws Exception {
        //JJBMCOptions.forceInliningMethods = false;
        return getTestStream("FITests.java");
    }

    @TestFactory
    public Stream<DynamicTest> ppTests() throws Exception {
        return getTestStream("PPTests.java", (it) -> it.proofPreconditions = true);
    }

    @TestFactory
    public Stream<DynamicTest> runTestSuite() throws Exception {
        return getTestStream("TestSuite.java");
    }

    private static Stream<DynamicTest> getTestStream(String filename) throws Exception {
        return getTestStream(filename, (it) -> {
        });
    }

    private static Stream<DynamicTest> getTestStream(String filename, Consumer<JJBMCOptions> configure) throws Exception {
        return Utils.prepareParameters(Utils.SRC_TEST_RESOURCES.resolve("tests").resolve(filename))
                .map(it -> {
                    JJBMCOptions o = it.op().getOptions();
                    String displayName = o.getFileName().getFileName() + "::" + o.functionName;

                    return DynamicTest.dynamicTest(displayName,
                            () -> {
                                configure.accept(o);
                                Utils.runTests(it);
                            });
                });
    }
}
