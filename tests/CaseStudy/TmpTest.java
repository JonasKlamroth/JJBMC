package CaseStudy;

import TestAnnotations.Fails;
import TestAnnotations.Verifyable;
import org.cprover.CProver;

/**
 * Created by jklamroth on 12/18/18.
 */
public class TmpTest {
    int[] arr;
    TmpTest t2;
    public int pubInt;
    private int privInt;
    TmpTest[] objects;


    //@ assignable pubInt;
    @Fails
    private void methodInvAss(int i) {
        test();
    }

    //@ assignable arr[2..4];
    @Fails
    private void methodInvAss1(int i) {
        test1();
    }

    //@ requires arr != null && arr.length > 3;
    //@ assignable arr[1..3];
    @Verifyable
    private void methodInvAss2(int i) {
        test1();
    }

    //@ assignable t2;
    @Verifyable
    private void methodInvAss3(int i) {
        test2();
    }

    //@ assignable this.*;
    //@ requires arr != null && arr.length > 3;
    @Verifyable
    private void methodInvAss4(int i) {
        test1();
    }

    //@ assignable t2;
    @Fails
    private void methodInvAss5(int i) {
        test();
    }

    //@ assignable t2;
    @Fails
    private void methodInvAss6(int i) {
        test3();
    }

    private void test() {}

    //@ assignable arr[1..3];
    private void test1() {}

    //@ assignable t2;
    private void test2() {}

    //@ assignable objects;
    private void test3() {}
}
