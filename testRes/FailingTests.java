import testannotations.Fails;
import testannotations.Unwind;
import testannotations.Verifyable;

/**
 * Created by jklamroth on 1/3/19.
 */
public class FailingTests {

    //@ requires (arr != null && arr.length == 5);
    //@ requires (\forall int i; i >= 0 && i < 5; arr[i] == i);
    //@ ensures false;
    @Fails
    private void arrayTest(int[] arr) {

    }

    @Fails
    @Unwind(number = 5)
    private void arrayTest2() {
        int[] arr = new int[4];
        //@ assert (\forall int i; i >= 0 && i < 4; arr[i] == 0);
    }

    @Fails
    @Unwind(number = 5)
    private void arrayTest1() {
        int[] arr = new int[4];
        //@ assume (\forall int i; i >= 0 && i < 4; arr[i] == i);
        //@ assert false;
    }

    //@ requires a != null && 0 <= r < a.length;
    //@ ensures (\forall int i; 0 <= i < r; a[i] == \old(a[i]));
    @Verifyable
    public void testOldQuantifierBound(int[] a, int r) {
        r++;
    }
}
