/**
 * Created by jklamroth on 9/18/18.
 */
public class Test2 {
    private int privInt;
    public int pubInt;

    //@ requires 1 < 0;
    //@ ensures true;
    private void test() {
        int locInt = 0;
        locInt++;
        System.out.println("This is just a test." + locInt);
    }

    public void test1() {
        test();
    }
}
