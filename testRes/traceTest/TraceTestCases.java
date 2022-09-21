/**
 * Created by jklamroth on 12/18/18.
 */
public class TraceTestCases {
    class IntObject {
        public int i = 0;
    }
    private int privInt = 0;
    private TraceTestCases tt = null;
    public int pubInt = 0;
    int[] table = new int[2];
    Object[] otable;
    IntObject[] iotable;

    public TraceTestCases(int i) {
        privInt = i;
    }



    /*@ private normal_behavior
      @ requires j == 3;
      @ ensures false;
      @*/
    public void test(int j) {
        int k = 0;
        //test2(5);
        tt = new TraceTestCases(2);
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
        iotable[0].i = 5;
    }

    //@ ensures otable == null;
    void test4() {
        this.otable = new Object[5];
    }

    //@ ensures table == null;
    void test5() {
    }

    //@ requires size == 2;
    //@ ensures iotable == null;
    void test6(int size) {
        this.iotable = new IntObject[size];
    }
}
