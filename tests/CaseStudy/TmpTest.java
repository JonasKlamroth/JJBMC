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

    //@ ensures (\forall int j; j >= 0 && j <= 10; j > i) ==> i < 0;
    @Verifyable
    private void impliesTest2(int i) {
    }
}
