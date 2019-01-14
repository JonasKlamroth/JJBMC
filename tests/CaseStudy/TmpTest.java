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

    //@ requires (\exists int i; i >= 0 && i < 10; i > 5);
    //@ ensures false;
    @Fails
    private void requiresTest() {
    }

    //@ requires false;
    //@ ensures false;
    @Verifyable
    private void requiresTest2(int j) {
    }

    //@ requires j > 10;
    //@ requires (\exists int i; i >= 0 && i < 10; i > j);
    //@ ensures false;
    @Verifyable
    private void requiresTest1(int j) {
    }

    //@ requires (\forall int i; i >= 0 && i < 10; \exists int j; j >= 0 && j <= 10; j > i);
    //@ ensures false;
    @Fails
    private void requiresTest3() {
    }

    //@ requires (\forall int i; i >= 0 && i < 10; \exists int j; j >= 0 && j < 10; j > i);
    //@ ensures false;
    @Verifyable
    private void requiresTest4() {
    }

    //@ requires (\exists int i; i >= 0 && i < 10; \exists int j; j >= 0 && j <= 10; j > i);
    //@ ensures false;
    @Fails
    private void requiresTest5() {
    }

    //@ requires (\exists int i; i >= 0 && i < 0; \exists int j; j >= 0 && j < 10; j > i);
    //@ ensures false;
    @Verifyable
    private void requiresTest6() {
    }

    //@ requires (\forall int i; i >= 0 && i < 10; \forall int j; j >= 10 && j <= 10; j > i);
    //@ ensures false;
    @Fails
    private void requiresTest7() {
    }

    //@ requires (\forall int i; i >= 0 && i < 10; \forall int j; j >= 0 && j < 10; j > i);
    //@ ensures false;
    @Verifyable
    private void requiresTest8() {
    }

}
