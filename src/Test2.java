/**
 * Created by jklamroth on 9/18/18.
 */
public class Test2 {
    private int privInt;
    public int pubInt;
    Test2 t2 = new Test2();
    int[] arr;

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

    /*@ assignable privInt, t2.t2, t2.arr[0];
      @ */
    private void assignalbeTest() {
        t2 = new Test2();
        t2.pubInt = 5;
        t2.t2 = new Test2();
        t2.t2.pubInt = 10;
        t2.arr = new int[10];
        t2.arr[5] = 10;
        privInt = 0;
    }

    /*@ assignable arr[0];
      @*/
    private void assignableTest2() {
        arr[0] = 5;
    }
}
