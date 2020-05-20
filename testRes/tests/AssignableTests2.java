package tests;

import TestAnnotations.Fails;
import TestAnnotations.Verifyable;

class TestSuite {
    private int privInt = 0;
    public int pubInt;
    TestSuite t2;
    TestSuite t3;
    int[] arr;
    TestSuite[] objects;
}

/**
 * Created by jklamroth on 1/11/19.
 */
public class AssignableTests2 {
    private int privInt = 0;
    public int pubInt;
    TestSuite t2;
    TestSuite t3;
    int[] arr;
    TestSuite[] objects;

    //@ requires t2 != null && t2.objects != null && t2.objects.length >= 1 && t2.objects[0] != null;
    //@ assignable t2.objects[0..1].t2;
    @Verifyable
    private void assignableTest14() {
        t2.objects[0].t2 = new TestSuite();
    }

    //@ requires t2 != null && t2.objects != null && t2.objects.length >= 1 && t2.objects[2] != null;
    //@ assignable t2.objects[0..1].t2;
    @Fails
    private void assignableTest15() {
        t2.objects[2].t2 = new TestSuite();
    }


}
