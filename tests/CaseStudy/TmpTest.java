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


    //@ assignable \nothing;
    @Verifyable
    private void assignableTest16() {
        int i = 0;
        ++i;
        assert i == 1;
    }
}
