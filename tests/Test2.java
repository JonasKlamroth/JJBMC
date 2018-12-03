/**
 * Created by jklamroth on 9/18/18.
 */
public class Test2 {
    private int privInt = 0;
    public int pubInt;
    Test2 t2;
    int[] arr;

    //@ requires true;
    private void tmptest(int i ) {
        return;
    }

    //@ requires 1 < 0;
    //@ ensures true;
    private void test() {
        int locInt = 0;
        locInt++;
        privInt = 0;
        System.out.println("This is just a test." + locInt);
    }

    //@ requires  i > 0;
    //@ ensures i > 1;
    public int test1(int i) {
        return i + 1;
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
    public void quantTest3() {
        System.out.println("this is basically a lemma.");
    }

    //@ requires (\forall int i; i > 0 && i < 10; 3 + 10 > i);
    //@ requires (\exists int i; i > 0 && i < 10; 3 + 10 > i);
    //@ ensures (\forall int i; i > 0 && i < 10; 3 + 10 > i);
    //@ ensures (\exists int i; i > 0 && i < 10; 3 + 10 > i);
    public void quantTest4() {
        System.out.println("this is basically a lemma.");
    }

    public void returnTest() {
        if(privInt == 0) {
            return;
        } else {
            privInt = 0;
        }
    }

    //@ requires true;
    //@ ensures false;
    public void loopTest() {
        int[] arr = new int[10];
        //@ loop_invariant i >= 0;
        //@ loop_invariant i > -1;
        //@ loop_modifies arr[*], arr[2 .. 4];
        for(int i = 0; i < 10; ++i) {
            arr[i] = i;
        }
    }

    public void loopTest1() {
        int[] arr = new int[10];
        //@ loop_invariant (\forall int j; j > 0 && j < 10; j > -1);
        //@ loop_invariant i > -1;
        //@ loop_modifies arr[*], arr[2 .. 4];
        for(int i = 0; i < 10; ++i) {
            arr[i] = i;
        }
    }

    /*@ assignable privInt;
      @ */
    private void assignalbeTest() {
        privInt = 0;
    }

    /*@ assignable t2;
      @ */
    private void assignalbeTest1(Test2 t3) {
        t3 = new Test2();
        t3.t2 = new Test2();
        privInt = 0;
    }

    /*@ assignable arr[5];
      @ */
    private void assignalbeTest10() {
        arr[1] = 5;
        arr[5] = 3;
    }

    /*@ assignable arr[*];
      @ */
    private void assignalbeTest3() {
        arr[3] = 5;
    }

    /*@ assignable arr[3..];
      @ */
    private void assignalbeTest4() {
        arr[4] = 2;
    }

    /*@ assignable arr[1..3], arr[4..5];
      @ */
    private void assignalbeTest41(int arr1[]) {
        arr1[4] = 2;
    }

    /*@ assignable t2.*;
      @ */
    private void assignalbeTest5(Test2 t3) {
        t3 = new Test2();
        t3.pubInt = 5;
        t3.t2 = new Test2();
        t3.t2.pubInt = 10;
        t3.arr = new int[10];
        t3.arr[5] = 10;
    }

    /*@ assignable t2.t2.pubInt;
      @ */
    private void assignalbeTest6(Test2 t3) {
        t3 = new Test2();
        t3.pubInt = 5;
        t3.t2 = new Test2();
        t3.t2.pubInt = 10;
    }

    /*@ assignable t2.arr[4];
      @ */
    private void assignalbeTest7(Test2 t3) {
        t3.arr[5] = 10;
    }

    private void assignalbeTest8() {
        int i = 5;
        i = 10;
        if(i > 10) {
            i = 20;
        }
    }

    private void assignalbeTest9() {
        if(privInt > 10) {
            privInt = 20;
        }
    }
}
