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
    int[] table;
    Object[] otable;
    public IntObject[] iotable;

    //@ ensures \result == 0;
    public int test() {
        return callee(1);
    }

    //@ requires i > 0;
    //@ ensures \result == 1;
    //@ assignable \nothing;
    public int callee(int i) {
        return i - 1;
    }
}
