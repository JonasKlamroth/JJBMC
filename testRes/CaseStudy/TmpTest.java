package CaseStudy;

import TestAnnotations.Verifyable;

/**
 * Created by jklamroth on 12/18/18.
 */
public class TmpTest {
    int[] arr;
    TmpTest t2;
    public int pubInt;
    private int privInt;
    TmpTest[] objects;

    @Verifyable
    private void blockContractTest(int i, int j, int k) {
        //@ assume i >= 0 && i < j && j < k && k <= 2;
        assert false;
    }
}
