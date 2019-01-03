package CaseStudy;

import TestAnnotations.Fails;
import TestAnnotations.Verifyable;

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

    @Fails
    private void assertTest2() {
        //@ assert (\forall int i; i > 0 && i < 10; i > 2);
    }

    @Verifyable
    private void assertTest3() {
        //@ assert (\forall int i; i > 0 && i < 10; i > 0);
    }

    @Verifyable
    private void assertTest4() {
        //@ assert (\exists int i; i > 0 && i < 10; i > 5);
    }

    @Fails
    private void assertTest5() {
        //@ assert (\exists int i; i > 0 && i < 10; i > 11);
    }

    @Verifyable
    private void assumeTest1() {
        int i = 0;
        //@ assume i > 0;
        //@ assert i > -1;
    }

    @Verifyable
    private void assumeTest2() {
        int[] arr = new int[2];
        //@ assume (\forall int i; i >= 0 && i < 2; arr[i] == 2);
        //@ assert (\exists int i; i >= 0 && i < 2; arr[i] == 2);
    }

    @Fails
    private void assumeTest4() {
        int[] arr = new int[2];
        //@ assert (\forall int i; i >= 0 && i < 2; arr[i] == 2);
    }

    @Fails
    private void assumeTest3() {
        arr = new int[2];
        //@ assume (\forall int i; i >= 0 && i < 2; arr[i] == 2);
        //@ assert false;
        //@ assert (\forall int i; i >= 0 && i < 2; arr[i] == 2);
    }
}
