package CaseStudy;

import TestAnnotations.Fails;
import TestAnnotations.Unwind;
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

    //@ assignable \everything;
    @Verifyable
    private void test() {
        negatedTest();
    }


    //@ ensures \old(pubInt) == pubInt + 1;
    //@ assignable pubInt;
    @Verifyable
    private void negatedTest() {
        pubInt--;
    }
}
