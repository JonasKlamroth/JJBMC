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



    /*@ private normal_behavior
      @ requires j == 3;
      @ ensures false;
      @*/
    public void test(int j) {
        int k = 0;
        //test2(5);
        tt = new TmpTest(2);
        this.table = new int[]{1, 2, 3, 4};
        table[j] = 2;
    }

    /*@ private normal_behavior
      @ ensures false;
      @ assignable privInt;
      @*/
    public void test2(int z) {
        this.privInt = z;
    }

    //@ ensures false;
    public void test3() {
        iotable = new IntObject[]{new IntObject(), new IntObject()};
        //iotable[0].i = 5; TODO
    }
}
