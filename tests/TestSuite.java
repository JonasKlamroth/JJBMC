import TestAnnotations.Fails;
import TestAnnotations.Unwind;
import TestAnnotations.Verifyable;

/**
 * Created by jklamroth on 9/18/18.
 */
public class TestSuite {
    private int privInt = 0;
    public int pubInt;
    TestSuite t2;
    int[] arr;
    TestSuite[] objects;

    //@ requires  i > 0 && i < 10000;
    //@ ensures \result == i + 1;
    @Verifyable
    public int test1(int i) {
        return i + 1;
    }

    //@ requires (\forall int i; i > 0 && i < 10; i > 0);
    //@ requires (\exists int i; i > 0 && i < 10; i == 5);
    @Verifyable
    public void quantTest() {
        //this is basically a lemma
    }

    //@ requires (\forall int i; i > 0 && i < 10; 3 + 10 > i);
    //@ requires (\exists int i; i > 0 && i < 10; 3 + 10 > i);
    //@ ensures (\forall int i; i > 0 && i < 10; 3 + 10 > i);
    //@ ensures (\exists int i; i > 0 && i < 10; 3 + 10 > i);
    @Verifyable
    public void quantTest4() {
        //this is basically a lemma
    }


    //@ assignable privInt;
    @Verifyable
    private void returnTest() {
        if(privInt == 0) {
            return;
        } else {
            privInt = 0;
        }
    }


    @Unwind(number = 11)
    @Verifyable
    public void loopTest1() {
        int[] arr = new int[10];
        //@ loop_invariant i > -1 && i <= 10;
        //@ loop_invariant (\forall int j; j >= 0 && j < i; arr[j] == j);
        //@ loop_modifies arr[*];
        //@ decreases 11 - i;
        for(int i = 0; i < 10; ++i) {
            arr[i] = i;
        }
    }

    @Unwind(number = 11)
    @Fails
    public void decreasesTest1() {
        int[] arr = new int[10];
        //@ loop_invariant i > -1 && i <= 10;
        //@ loop_invariant (\forall int j; j >= 0 && j < i; arr[j] == j);
        //@ loop_modifies arr[*];
        //@ decreases 11 + i;
        for(int i = 0; i < 10; ++i) {
            arr[i] = i;
        }
    }

    @Unwind(number = 11)
    @Verifyable
    public void decreasesTest2() {
        int[] arr = new int[10];
        //@ loop_invariant i > -1 && i <= 10;
        //@ loop_invariant (\forall int j; j >= 0 && j < i; arr[j] == j);
        //@ loop_modifies arr[*];
        for(int i = 0; i < 10; ++i) {
            arr[i] = i;
        }
    }

    @Unwind(number = 11)
    @Fails
    public void decreasesTest3() {
        int[] arr = new int[10];
        //@ loop_invariant i > -1 && i <= 10;
        //@ loop_invariant (\forall int j; j >= 0 && j < i; arr[j] == j);
        //@ loop_modifies arr[*];
        //@ decreases 5 - i;
        for(int i = 0; i < 10; ++i) {
            arr[i] = i;
        }
    }

    /*@ assignable privInt;
      @ */
    @Verifyable
    private void assignalbeTest() {
        privInt = 0;
    }

    /*@ assignable t2;
      @ */
    @Fails
    private void assignalbeTest1(TestSuite t3) {
        t3 = new TestSuite();
        t3.t2 = new TestSuite();
        privInt = 0;
    }

    /*@ assignable arr[5];
      @ */
    @Fails
    private void assignalbeTest10() {
        arr[1] = 5;
        arr[5] = 3;
    }

    /*@ assignable \nothing;
      @ */
    @Fails
    private void assigableNothingTest() {
        arr[1] = 5;
        arr[5] = 3;
    }

    /*@ requires arr != null && arr.length > 5;
      @ assignable \everything;
      @ */
    @Verifyable
    private void assigableEverythingTest() {
        arr[1] = 5;
        arr[5] = 3;
        t2 = new TestSuite();
        privInt = 12039;
    }

    //@ requires arr != null && arr.length > 3;
    //@ assignable arr[*];
    @Verifyable
    private void assignalbeTest3() {
        arr[3] = 5;
    }

    /*@ requires arr != null && arr.length > 4;
      @ assignable arr[3..];
      @ */
    @Verifyable
    private void assignalbeTest4() {
        arr[4] = 2;
    }

    /*@ requires arr != null && arr.length > 5;
      @ assignable arr[1..3], arr[4..5];
      @ */
    @Verifyable
    private void assignalbeTest41(int arr1[]) {
        arr1[4] = 2;
    }

    /*@ assignable t2.*;
      @ */
    @Fails
    private void assignalbeTest5(TestSuite t3) {
        t3 = new TestSuite();
        t3.pubInt = 5;
        t3.t2 = new TestSuite();
        t3.t2.pubInt = 10;
        t3.arr = new int[10];
        t3.arr[5] = 10;
    }

    /*@ assignable t2.t2.pubInt;
      @ */
    @Fails
    private void assignalbeTest6(TestSuite t3) {
        t3 = new TestSuite();
        t3.pubInt = 5;
        t3.t2 = new TestSuite();
        t3.t2.pubInt = 10;
    }



    @Verifyable
    private void assignalbeTest8() {
        int i = 5;
        i = 10;
        if(i > 10) {
            i = 20;
        }
    }

    @Verifyable
    private void assignalbeTest9() {
        if(privInt > 10) {
            privInt = 20;
        }
    }

    /*
    //@ requires t != null;
    //@ assignable t2.*;
    @TestAnnotations.Fails
    private void assignableTest10(TestSuite t) {
        TestSuite testSuite = new TestSuite();
        testSuite = t;
        testSuite.arr = new int[10];
    }*/

    //@ requires t2 != null;
    //@ assignable t2.*;
    @Verifyable
    private void assignableTest11() {
        TestSuite testSuite = new TestSuite();
        testSuite = t2;
        testSuite.arr = new int[10];
    }

    /*
    //@ requires t2 != null;
    //@ assignable t2.*;
    @TestAnnotations.Verifyable
    private void uninterpretedFunctionTest() {
        Object o = new Object();
        CProver.assume(CProver.uninterpreted_fresh(o));
        assert(CProver.uninterpreted_fresh(o));
    }*/

    @Verifyable
    private void blockContractTest() {
        int i = 0;
        //@ requires i == 0;
        //@ ensures i == 6;
        {
            i = 5;
            i++;
        }
    }

    @Fails
    private void blockContractTest1() {
        int i = 0;
        //@ requires i == 0;
        //@ ensures i == 7;
        {
            i = 5;
            i++;
        }
    }

    @Fails
    private void blockContractTest2() {
        int i = 0;
        //@ requires i == 1;
        //@ ensures i == 6;
        {
            i = 5;
            i++;
        }
    }

    //@ ensures \result == 5;
    @Verifyable
    private int methodInvcationTest() {
        int i = 4;
        i = test1(i);
        return i;
    }

    //@ ensures \result == 5;
    @Verifyable
    private int methodInvcationTest2() {
        int i = 4;
        return fakeTest(i);
    }

    //@ ensures \result == 0;
    @Fails
    private int methodInvcationTest3() {
        int i = 4;
        return fakeTest(i);
    }

    //@ ensures \result == 56;
    @Fails
    private int methodInvcationTest4() {
        int i = 4;
        return fakeTest(i);
    }

    //@ ensures \result == 56;
    @Verifyable
    private int methodInvcationTest5() {
        int i = 4;
        return fakeTest();
    }

    //@ assignable t2;
    @Verifyable
    private int methodInvcationTest6() {
        calledMethod();
        return 0;
    }

    @Fails
    public void havocTest() {
        assert pubInt == 0;
    }

    @Fails
    public void havocTest1() {
        assert t2 == null;
    }

    @Fails
    public void havocTest2() {
        assert arr.length == 0;
    }

    //@ requires arr != null && arr.length >= 1;
    @Fails
    public void havocTest3(int[] arr) {
        assert arr[0] == 0;
    }

    //@ requires arr != null && arr.length == 2 && arr[0] == 5 && arr[1] == 1;
    //@ ensures false;
    @Fails
    public void havocTest4(int[] arr) {
    }

    /*
    //@ requires arr != null && arr.length == 10;
    //@ requires (\forall int i; i >= 0 && i < 10; arr[i] == i);
    //@ ensures false;
    @Fails
    public void havocTest5(int[] arr) {
    }*/

    //@ requires arr != null && arr.length == 5;
    //@ requires (\forall int i; i >= 0 && i < 10; arr[i] == i);
    //@ ensures false;
    @Fails
    private void havocTest6() {
    }

    //@ ensures \result == 5;
    private int fakeTest(int i) {
        return 0;
    }

    private int fakeTest() {
        return 56;
    }

    //@ assignable t2;
    private void calledMethod() {
        t2 = new TestSuite();
    }

    //@ requires objects != null && objects.length >= 1 && objects[0] != null;
    //@ assignable objects[0..3].t2;
    @Verifyable
    private void assignableTest12() {
        objects[0].t2 = new TestSuite();
    }

    //@ requires objects != null && objects.length >= 1 && objects[0] != null;
    //@ assignable objects[0..3].t2;
    @Fails
    private void assignableTest13() {
        objects[0] = new TestSuite();
    }

    //@ requires t2 != null && t2.objects != null && t2.objects.length >= 1 && t2.objects[0] != null;
    //@ assignable t2.objects[0..1].t2;
    @Verifyable
    private void assignableTest14() {
        t2.objects[0].t2 = new TestSuite();
    }

    //@ requires t2 != null && t2.objects != null && t2.objects.length >= 1 && t2.objects[2] != null;
    //@ assignable t2.objects[0..1].t2;
    @Fails
    private void assignableTest15() {
        t2.objects[2].t2 = new TestSuite();
    }

    //@ assignable \nothing;
    @Verifyable
    private void assignableTest16() {
        TestSuite t2 = new TestSuite();
        t2 = new TestSuite();
    }

    //@ assignable \nothing;
    @Fails
    private void assignableTest17() {
        TestSuite t2 = new TestSuite();
        t2 = new TestSuite();
        this.t2 = new TestSuite();
    }

    @Verifyable
    private void assignableTest18() {
        this.t2 = new TestSuite();
    }

    //@ ensures \result == 10;
    @Verifyable
    @Unwind(number = 6)
    private int testNoInvariantLoop() {
        int res = 0;
        for(int i = 0; i < 5; i++) {
            res += i;
        }
        return res;
    }

    //@ ensures i > 0 ==> i > -1;
    @Verifyable
    private void impliesTest(int i) {
    }

    //@ ensures i > 0 ==> i > 1;
    @Fails
    private void impliesTest1(int i) {
    }

    //@ ensures i > 0 <==> i >= 1;
    @Verifyable
    private void equivalenceTest(int i) {
    }

    //@ ensures i > 0 <==> i > 1;
    @Fails
    private void equivalenceTest1(int i) {
    }

    //@ ensures (\forall int j; j >= 0 && j <= 10; j > i) ==> i < 0;
    @Verifyable
    private void impliesTest2(int i) {
    }

    //@ ensures (\exists int j; j >= 0 && j <= 10; j > i) ==> i < 0;
    @Fails
    private void impliesTest3(int i) {
    }

    //@ requires privInt == 0;
    //@ ensures privInt == 10;
    @Verifyable
    @Unwind(number = 11)
    private void assignableTest19() {
        for(; privInt < 10; privInt++) {
            int i = 0;
        }
    }

    //@ requires privInt == 0;
    //@ assignable \nothing;
    //@ ensures privInt == 10;
    @Fails
    @Unwind(number = 11)
    private void assignableTest20() {
        for(; privInt < 10; privInt++) {
            int i = 0;
        }
    }

    //@ assignable \nothing;
    @Fails
    private void assignableTest21() {
        privInt++;
    }

    //@ requires privInt == 0;
    //@ ensures privInt == 1;
    //@ assignable privInt;
    @Verifyable
    private void assignableTest22() {
        privInt++;
    }

    //@ requires privInt == 0;
    //@ ensures privInt == 1;
    //@ assignable privInt;
    @Verifyable
    private void assignableTest23() {
        if(privInt++ > 0) {
            return;
        }
    }

    //@ requires privInt == 0;
    //@ ensures privInt == 1;
    //@ assignable \nothing;
    @Fails
    private void assignableTest24() {
        if(privInt++ > 0) {
            return;
        }
    }

    //@ requires privInt == 0;
    //@ ensures privInt == 1;
    //@ assignable \nothing;
    @Fails
    private void assignableTest25() {
        fakeTest(privInt++);
    }

    //@ requires privInt == 0;
    //@ ensures privInt == 1;
    //@ assignable \everything;
    @Verifyable
    private void assignableTest26() {
        fakeTest(privInt++);
    }

    //@ assignable \nothing;
    @Fails
    private void assignableTest27() {
        privInt += 5;
    }

    //@ requires privInt == 0;
    //@ ensures privInt == 5;
    //@ assignable privInt;
    @Verifyable
    private void assignableTest28() {
        privInt += 5;
    }

    @Fails
    private void assertTest() {
        //@ assert(0 > 1);
    }

    @Fails
    private void assertTest2() {
        //@ assert (\forall int i; i > 0 && i < 10; i > 2);
    }

    @Verifyable
    private void assertTest3() {
        //@ assert (\forall int i; i > 0 && i < 10; i > 0);
    }

    @Verifyable
    private void assertTest4() {
        //@ assert (\exists int i; i > 0 && i < 10; i > 5);
    }

    @Fails
    private void assertTest5() {
        //@ assert (\exists int i; i > 0 && i < 10; i > 11);
    }

    @Verifyable
    private void assumeTest1() {
        int i = 0;
        //@ assume i > 0;
        //@ assert i > -1;
    }

    @Verifyable
    private void assumeTest2() {
        int[] arr = new int[2];
        //@ assume (\forall int i; i >= 0 && i < 2; arr[i] == 2);
        //@ assert (\exists int i; i >= 0 && i < 2; arr[i] == 2);
    }

    @Fails
    private void assumeTest4() {
        int[] arr = new int[2];
        //@ assert (\forall int i; i >= 0 && i < 2; arr[i] == 2);
    }

    //@ ensures \result == 2.0f;
    @Verifyable
    private float floatTest() {
        float f = 1.0f;
        f += 1.0f;
        return f;
    }

    //@ ensures (\exists int i; i >= 0 && i < 3; (\forall int j; j >= 0 && j < 3; j > i));
    @Fails
    private void nestedQuantifierTest() {}

    //@ ensures (\forall int i; i >= 0 && i < 3; (\exists int j; j >= 0 && j < 3; j > i));
    @Fails
    private void nestedQuantifierTest1() {}

    //@ ensures (\forall int i; i >= 0 && i < 3; (\exists int j; j >= -1 && j < 3; i > j));
    @Verifyable
    private void nestedQuantifierTest3() {}

    //@ ensures (\exists int i; i >= 0 && i < 3; (\forall int j; j >= 0 && j < 2; i > j));
    @Verifyable
    private void nestedQuantifierTest2() {}

    //@ ensures !(\forall int i; i >= 0 && i < 3; (\exists int j; j >= 0 && j < 3; j > i));
    @Verifyable
    private void negatedQuantifierTest() {}

    //@ ensures !(\forall int i; i >= 0 && i < 3; (\exists int j; j >= 0 && j < 3; j > i));
    @Verifyable
    private void negatedQuantifierTest1() {}

    //@ ensures !(\forall int i; i >= 0 && i < 3; (\exists int j; j >= -1 && j < 3; i > j));
    @Fails
    private void negatedQuantifierTest3() {}

    //@ ensures !(\exists int i; i >= 0 && i < 3; (\forall int j; j >= 0 && j < 2; i > j));
    @Fails
    private void negatedQuantifierTest2() {}

    //@ ensures (\exists int i; i >= 0 && i < 3; !(\forall int j; j >= 0 && j < 2; i > j));
    @Verifyable
    private void negatedQuantifierTest4() {}

    //@ ensures (\exists int i; i >= 3 && i < 5; !(\forall int j; j >= 0 && j < 2; i > j));
    @Fails
    private void negatedQuantifierTest5() {}
}
