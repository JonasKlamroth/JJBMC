package CaseStudy;

/**
 * Created by jklamroth on 12/18/18.
 */
public class TmpTest {
    private int privInt = 0;
    private TmpTest tt = null;
    public int pubInt = 0;





    //@ ensures \result == 4;
    private int test1() {
        int res = 0;
        for(int i = 0; i++ < 3; res = inc(res)) {
        }
        return res;
    }

    //@ ensures \result == i + 1;
    private int inc(int i) {
        return i+1;
    }

}
