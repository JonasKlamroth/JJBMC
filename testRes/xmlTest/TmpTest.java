
import org.cprover.CProver;

public class TmpTest {

    public TmpTest() {
        {
        }
        try {
        } catch (TmpTest.ReturnException ex) {
        }
        {
        }
    }
    /*@
    public behavior
      assignable \nothing;
      signals () false;
   */

    public static TmpTest TmpTestSymb() {
        return new TmpTest();
    }
    private int privInt = 0;
    /*@ non_null */
    private TmpTest tt = null;

    private void test(/*@ non_null */
            int[] a) {
        {
        }
        {
            boolean b_0 = true;
            if (a != null && a.length > 2) {
                for (int quantVar0i = 0; 0 <= quantVar0i && a.length - 1 - 1 >= quantVar0i; ++quantVar0i) {
                    b_0 = b_0 && a[quantVar0i] < a[quantVar0i + 1];
                }
            }
            CProver.assume(a != null && a.length > 2 && (b_0));
        }
        try {
            a = new int[]{a[0], a[1]};
            for (int i = 0; i < a.length; ++i) {
                if (a[i] % 2 == 0) {
                    a[i]++;
                }
            }
            privInt = 0;
            privInt++;
            this.privInt = 3;
            tt = new TmpTest();
            tt.privInt++;
            /*@ non_null */
            TmpTest t = new TmpTest();
            t.privInt = 2;
            /*@ non_null */
            int[] b = new int[]{0, 1, 2};
            assert false;
        } catch (TmpTest.ReturnException ex) {
        }
        {
        }
    }

    private static void test2(int i0) {
        try {
            {
                int i = 0;
            }
            {
                int j = 0;
            }
            assert false;
        } catch (TmpTest.ReturnException ex) {
        }
    }

    public static class ReturnException extends java.lang.RuntimeException {
    }
}
