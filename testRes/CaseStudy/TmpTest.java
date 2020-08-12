package CaseStudy;


/**
 * Created by jklamroth on 12/18/18.
 */
public class TmpTest {
    int[] arr;
    TmpTest t2;
    public int pubInt;
    private int privInt;
    int i;
    TmpTest[] objects;

    /*@ invariant
      @ i == 1;
      @*/

    //@ requires (\forall int i; i >= 0 && i < arr.length; arr[i] == 1);
    private void blockContractTest() {
        int sum = 0;
        while(sum < 10) {
            sum += 3;
        }
        assert sum == 12;
    }
}
