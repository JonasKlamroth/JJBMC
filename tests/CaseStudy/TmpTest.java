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

    /*@ assignable t2.t2.pubInt;
      @ */
    @Fails
    private void assignalbeTest6(TmpTest t3) {
        t3 = new TmpTest();
        t3.pubInt = 5;
        t3.t2 = new TmpTest();
        t3.t2.pubInt = 10;
    }

}
