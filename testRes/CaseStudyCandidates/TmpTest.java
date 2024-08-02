package CaseStudy;



/**
 * Created by jklamroth on 12/18/18.
 */
public class TmpTest {
    class IntObject {
        public int i = 0;
    }

    private int privInt = 0;
    private TmpTest tt = null;
    public int pubInt = 0;
    public int[] arr;
    Object[] otable;
    public IntObject[] iotable;

    //@ requires 0 <= pow < 32;
    //@ ensures \result == (1 << pow);
    public int pow2(int pow) {
        int res = 1;
        for(int i = 0; i < pow; ++i) {
            res *= 2;
        }
        return res;
    }

    //@ requires 0 <= pow < 32;
    //@ ensures \result == (1 << pow);
    //@ assignable \nothing;
    public int pow2v2(int pow) {
        if (pow == 0) {
            return 1;
        }
        return 2 * pow2v2(pow - 1);
    }
}