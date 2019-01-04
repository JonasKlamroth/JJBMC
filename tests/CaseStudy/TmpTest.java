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

    //@ ensures (\exists int i; i >= 0 && i < 3; (\forall int j; j >= 0 && j < 3; j > i));
    @Fails
    private void nestedQuantifierTest() {}

    //@ ensures (\forall int i; i >= 0 && i < 3; (\exists int j; j >= 0 && j < 3; j > i));
    @Fails
    private void nestedQuantifierTest1() {}

    //@ ensures (\forall int i; i >= 0 && i < 3; (\exists int j; j >= -1 && j < 3; i > j));
    @Verifyable
    private void nestedQuantifierTest3() {}

    //@ ensures (\exists int i; i >= 0 && i < 3; (\forall int j; j >= 0 && j < 2; i > j));
    @Verifyable
    private void nestedQuantifierTest2() {}

    //@ ensures !(\forall int i; i >= 0 && i < 3; (\exists int j; j >= 0 && j < 3; j > i));
    @Verifyable
    private void negatedQuantifierTest() {}

    //@ ensures !(\forall int i; i >= 0 && i < 3; (\exists int j; j >= 0 && j < 3; j > i));
    @Verifyable
    private void negatedQuantifierTest1() {}

    //@ ensures !(\forall int i; i >= 0 && i < 3; (\exists int j; j >= -1 && j < 3; i > j));
    @Fails
    private void negatedQuantifierTest3() {}

    //@ ensures !(\exists int i; i >= 0 && i < 3; (\forall int j; j >= 0 && j < 2; i > j));
    @Fails
    private void negatedQuantifierTest2() {}

    //@ ensures (\exists int i; i >= 0 && i < 3; !(\forall int j; j >= 0 && j < 2; i > j));
    @Verifyable
    private void negatedQuantifierTest4() {}

    //@ ensures (\exists int i; i >= 3 && i < 5; !(\forall int j; j >= 0 && j < 2; i > j));
    @Fails
    private void negatedQuantifierTest5() {}

}
