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
    IntObject[] iotable;



    /*@ requires a <= c && b <= d && a >= -1.f && a <= 1.f &&
      @         b >= -1.f && b <= 1.f &&
      @         c >= -1.f && c <= 1.f &&
      @         d >= -1.f && d <= 1.f;
      @ ensures \result;
      @*/
    public static boolean floatTest(float a, float b, float c, float d) {
        return a + b <= c + d;
    }
}
