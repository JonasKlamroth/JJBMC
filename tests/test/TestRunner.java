package test;

import org.junit.internal.TextListener;
import org.junit.runner.JUnitCore;

public class TestRunner {
    public static void main(String[] args) {
        JUnitCore junit = new JUnitCore();
        junit.addListener(new TextListener(System.out));
        junit.run(AssignableTests.class);
        junit.run(AssignableTests2.class);
        junit.run(TestSuiteTests.class);
    }
}
