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
    private int privInt;
    /*

    @Fails
    public void test(int arr[]) {
        CProver.assume(arr != null);
        CProver.assume(arr.length == 6);
        CProver.assume(arr[0] != 0 || arr[0] == 0);

        assert(false);
    }*/

    @Fails
    private void assumeTest() {
        {
            //@ assume false;
        }
        assert false;
    }

}
