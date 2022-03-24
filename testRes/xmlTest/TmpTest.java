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
    int[] table = new int[2];
    Object[] otable;
    IntObject[] iotable;

    public TmpTest(int i) {
        privInt = i;
    }



    //@ ensures (\forall int i; 0 <= i < 3; i < 1);
    public void test(int j) {
        int k = 0;
        test2(5);
        tt = new TmpTest(2);
        this.table = new int[]{1, 2};
        table[j] = 2;
    }

    public void test2(int z) {
        this.privInt = z;
    }
}
