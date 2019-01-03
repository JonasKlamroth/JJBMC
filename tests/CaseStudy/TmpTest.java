package CaseStudy;

import TestAnnotations.Fails;

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

    /*@ assignable t2.arr[4];
      @ */
    @Fails
    private void assignalbeTest7(TmpTest t3) {
        t3.arr[5] = 10;
    }

    //@ assignable \nothing;
    @Fails
    private void assignableTest27() {
        privInt += 5;
    }
}
