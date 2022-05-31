package test;

import cli.CLI;
import cli.CostumPrintStream;
import java.io.File;
import java.io.IOException;
import java.util.Collection;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import translation.FunctionNameVisitor;
import utils.Parallelized;
import utils.Utils;

@RunWith(Parallelized.class)
public class TestSuiteTests {
    public static final int numThreads = 16;

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
    public static Collection<Object[]> getParameters() {
        init();
        return Utils.prepareParameters(Utils.baseTestFolder + "tests" + File.separator + "TestSuite.java");
    }

    @Test
    public void runTestSuite() throws IOException, InterruptedException {
        Utils.runTests(classFile, function, unwind, behaviour, parentFolder);
    }

}
