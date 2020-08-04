package CaseStudy;


/**
 * Created by jklamroth on 12/18/18.
 */
public class TmpTest {
    int[] arr;
    TmpTest t2;
    public int pubInt;
    private int privInt;
    TmpTest[] objects;

    private void blockContractTest() {
        int sum = 0;
        while(sum < 10) {
            sum += 3;
        }
        assert sum == 12;
    }
}
