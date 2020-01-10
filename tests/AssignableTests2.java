import junitparams.JUnitParamsRunner;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.io.IOException;
import java.util.Collection;

@RunWith(JUnitParamsRunner.class)
public class AssignableTests2 {
    @BeforeClass
    public static void init() {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
    }

    @AfterClass
    public static void after() {
        CLI.cleanUp();
    }

    public static Collection<Object[]> assignableParamter2() {
        init();
        return Utils.prepareParameters(Utils.baseTestFolder + "tests/AssignableTests2.java");
    }

    @Test
    @junitparams.Parameters(method = "assignableParamter2")
    public void runAssignableTests2( String classFile,String function, String unwind,  FunctionNameVisitor.TestBehaviour behaviour, String parentFolder ) throws IOException, InterruptedException {
        Utils.runTests(classFile, function, unwind, behaviour, parentFolder);
    }
}
