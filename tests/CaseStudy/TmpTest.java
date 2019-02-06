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


    //@ ensures true || (\exists int i; 0 <= i && i < 1; 1/0 == 0);
    @Verifyable
    private void assignableTest16() {
    }
}
