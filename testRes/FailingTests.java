import TestAnnotations.Fails;
import TestAnnotations.Unwind;

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
}
