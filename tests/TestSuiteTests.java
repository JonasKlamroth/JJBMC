import junitparams.JUnitParamsRunner;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.io.IOException;
import java.util.Collection;

@RunWith(JUnitParamsRunner.class)
public class TestSuiteTests {

    @BeforeClass
    public static void init() {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
    }

    @AfterClass
    public static void after() {
        CLI.cleanUp();
    }

    public static Collection<Object[]> TestSuiteParameter() {
        init();
        return Utils.prepareParameters(Utils.baseTestFolder + "tests/TestSuite.java");
    }

    @Test
    @junitparams.Parameters(method = "TestSuiteParameter")
    public void runAssignableTests( String classFile,String function, String unwind,  FunctionNameVisitor.TestBehaviour behaviour, String parentFolder ) throws IOException, InterruptedException {
        Utils.runTests(classFile, function, unwind, behaviour, parentFolder);
    }

}
