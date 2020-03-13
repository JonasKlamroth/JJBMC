import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;
import java.util.Collection;

@RunWith(Parallelized.class)
public class AssignableTests {
    public static final int numThreads = 8;

    @Parameterized.Parameter(value = 0)
    public String classFile;
    @Parameterized.Parameter(value = 1)
    public String function;
    @Parameterized.Parameter(value = 2)
    public String unwind;
    @Parameterized.Parameter(value = 3)
    public FunctionNameVisitor.TestBehaviour behaviour;
    @Parameterized.Parameter(value = 4)
    public String parentFolder;

    @BeforeClass
    public static void init() {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
    }

    @AfterClass
    public static void after() {
        CLI.cleanUp();
    }

    @Parameterized.Parameters
    public static Collection<Object[]> assignableParamter() {
        init();
        return Utils.prepareParameters(Utils.baseTestFolder + "tests/AssignableTests.java");
    }

    @Test
    public void runAssignableTests() throws IOException, InterruptedException {
        Utils.runTests(classFile, function, unwind, behaviour, parentFolder);
    }
}
