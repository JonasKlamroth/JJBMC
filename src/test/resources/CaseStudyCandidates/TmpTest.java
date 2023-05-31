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



    /*@ requires a <= c && b <= d && a >= -1.f && a <= 1.f &&
      @         b >= -1.f && b <= 1.f &&
      @         c >= -1.f && c <= 1.f &&
      @         d >= -1.f && d <= 1.f;
      @ ensures \result;
      @*/
    public static boolean floatTest(float a, float b, float c, float d) {
        return a + b <= c + d;
    }

    /*@ requires arr != null && arr.length >= 2;
      @ ensures arr[0] == arr[1];
     */
    public static int[] test(int[] arr) {
        return arr;
    }

    /*@ ensures pubInt == 5 && \result.pubInt == 5;
      @*/
    public TmpTest test2(int val) {
        this.privInt = val;
        TmpTest tt = new TmpTest();
        tt.pubInt = 4;
        tt.table = new int[]{3, 0, 0};
        privInt = 2;
        pubInt = 3;
        return tt;
    }

    private void n() {
        int[] array = new int[1];
        int t = 0;
        //@ loop_invariant t == 0;
        //@ assignable array[t];
        while(true) {
            t = 0;
            mod(array, t);
        }
    }


    /*@
      @ requires iotable != null;
      @ requires (\forall int i; 0 <= i < iotable.length; iotable[i] != null);
      @ ensures (\forall int i; 0 <= i < iotable.length; iotable[i].i == 0);
      @*/
    public void testArrayInit() {

    }

    /*@ requires iotable != null;
      @ requires (\forall int i; 0 <= i < iotable.length; iotable[i] != null);
      @ requires (\exists int i; 0 <= i < iotable.length; iotable[i].i == 5);
      @ ensures !(\exists int i; 0 <= i < iotable.length; iotable[i] != null && iotable[i].i == 5);
     */
    private void testquant() {
            //for(int i = 0; i < iotable.length; ++i) {
                //if(iotable[i].i == 5) {
                    //iotable[i] = null;
                //}
            //}
    }

    //@ assignable array[t + 1];
    private void mod(int[] array, int t) {

    }
}
