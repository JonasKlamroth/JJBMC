package CaseStudy;

/**
 * Created by jklamroth on 12/18/18.
 */
public class TmpTest {
    private int privInt = 0;
    private TmpTest tt = null;

    //@ requires a != null && a.length > 2 && (\forall int i; i >= 0 && i < a.length - 1; a[i] < a[i+1]);
    private void test(int[] a) {
        a = new int[]{a[0], a[1]};
        for(int i = 0; i < a.length; ++i) {
            if(a[i] % 2 == 0) {
                a[i]++;
            }
        }
        privInt = 0;
        privInt++;
        this.privInt = 3;
        tt = new TmpTest();
        tt.privInt++;
        TmpTest t = new TmpTest();
        t.privInt = 2;
        int[] b = new int[]{ 0, 1, 2};
        assert false;
    }

    private static void test2(int i0) {
        {int i = 0;}
        {int j = 0;}
        assert false;
    }
}
