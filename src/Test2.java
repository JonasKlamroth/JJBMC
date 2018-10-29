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
        privInt = 0;
        Exception e = new Exception();
        System.out.println("This is just a test." + locInt);
    }

    public void test1() {
        test();
    }

    static public void test2() {
        for(int i = 0; i < 1; ++i) {
            System.out.println("empty");
        }
    }

    //@ requires (\forall int i; i > 0 && i < 10; i > 0);
    //@ requires (\exists int i; i > 0 && i < 10; i == 5);
    public void quantTest() {
        System.out.println("this is basically a lemma.");
    }

    //@ requires (\forall int i; i > 0 && i < 10; \forall int j; j > 10 && j < 20; j > i);
    //@ requires (\exists int i; i > 0 && i < 10; i == 5 && \forall int j; j > 10 && i < 20; j > i);
    public void quantTest2() {
        System.out.println("this is basically a lemma.");
    }

    //@ requires (\forall int i; i > 0 && i < 10; 3 + 10 > i);
    //@ requires (\exists int i; i > 0 && i < 10; 3 + 10 > i);
    //@ ensures (\forall int i; i > 0 && i < 10; 3 + 10 > i);
    //@ ensures (\exists int i; i > 0 && i < 10; 3 + 10 > i);
    public void quantTest3() {
        System.out.println("this is basically a lemma.");
    }

    public void returnTest() {
        if(privInt == 0) {
            return;
        } else {
            privInt = 0;
        }
    }
}
