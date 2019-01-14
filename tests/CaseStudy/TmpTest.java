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

    //@ ensures !(true && (\exists int i; i >= 0 && i < 5; i > 3));
    @Fails
    private void negatedTest() {
    }

    //@ ensures !(true && (\exists int i; i >= 0 && i < 5; i > 6));
    @Verifyable
    private void negatedTest1() {
    }

    //@ ensures (\forall int i; i >= 0 && i < 5; i > -1) || (\forall int j; j >= 0 && j < 5; j > 0);
    @Verifyable
    private void binaryTest() {
    }

    //@ ensures (\forall int i; i >= 0 && i < 5; i > -1) && (\forall int j; j >= 0 && j < 5; j > 0);
    @Fails
    private void binaryTest1() {
    }

    //@ ensures (\exists int i; i >= 0 && i < 5; i > -1) || (\exists int j; j >= 0 && j < 5; j > 0);
    @Verifyable
    private void binaryTest2() {
    }

    //@ ensures (\exists int i; i >= 0 && i < 5; i > -1) && (\exists int j; j >= 0 && j < 5; j > 6);
    @Fails
    private void binaryTest3() {
    }

}
