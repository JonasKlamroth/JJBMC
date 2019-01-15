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

    //@ requires true || (\forall int i; i >= 0 && i < 1; 1/i == 1/i);
    @Verifyable
    private void negatedTest() {
    }




}
