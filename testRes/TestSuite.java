package test;

import TestAnnotations.Fails;
import TestAnnotations.Unwind;
import TestAnnotations.Verifyable;

/**
 * Created by jklamroth on 9/18/18.
 */
class TestSuite {
    private int privInt = 0;
    public int pubInt;
    TestSuite t2;
    TestSuite t3;
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
    //@ requires (\exists int j; j > 0 && j < 10; 3 + 10 > j);
    //@ ensures (\forall int i; i > 0 && i < 10; 3 + 10 > i);
    //@ ensures (\exists int j; j > 0 && j < 10; 3 + 10 > j);
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

    //@ ensures (\exists int i; 0 <= i && i < 1; 1/0 == 0);
    @Fails
    private void quantifierTest() {
    }

    //@ assignable t2;
    private void calledMethod() {
        t2 = new TestSuite();
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

    @Verifyable
    private void trivialTest() {
        int i = 0;
        i = i + 5;
        //@ assert i == 5;
        i++;
        //@ assert i == 6;
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

    //@ ensures !(\forall int i; i >= 0 && i < 3; (\exists int j; j >= 0 && j < 3; j > i));
    @Verifyable
    private void negatedQuantifierTest() {}

    //@ ensures !(\forall int i; i >= 0 && i < 3; (\exists int j; j >= 0 && j < 3; j > i));
    @Verifyable
    private void negatedQuantifierTest1() {}

    //@ ensures !(\forall int i; i >= 0 && i < 3; (\exists int j; j >= -1 && j < 3; i > j));
    @Fails
    private void negatedQuantifierTest3() {}

    //@ ensures (\exists int i; i >= 0 && i < 3; !(\forall int j; j >= 0 && j < 2; i > j));
    @Verifyable
    private void negatedQuantifierTest4() {}

    //@ ensures (\exists int i; i >= 3 && i < 5; !(\forall int j; j >= 0 && j < 2; i > j));
    @Fails
    private void negatedQuantifierTest5() {}

    //@ ensures !(\exists int i; i >= 0 && i < 3; (\forall int j; j >= 0 && j < 2; i > j));
    @Fails
    private void negatedQuantifierTest2() {}

    //@ ensures (\exists int i; i >= 0 && i < 3; (\forall int j; j >= 0 && j < 2; i > j));
    @Verifyable
    private void nestedQuantifierTest2() {}

    //@ ensures (\forall int i; i >= 3 && i < 5; (\forall int j; j >= 0 && j < 2; i > j));
    @Verifyable
    private void nestedQuantifierTest4() {}

    //@ ensures (\forall int i; i >= 2 && i < 6; (\forall int j; j >= 0 && j < 3; i > j));
    @Fails
    private void nestedQuantifierTest5() {}

    //@ ensures (\exists int i; i >= 0 && i < 3; (\exists int j; j >= 0 && j < 2; i > j));
    @Verifyable
    private void nestedQuantifierTest6() {}

    //@ ensures (\exists int i; i >= -4 && i < 0; (\exists int j; j >= 0 && j < 2; i > j));
    @Fails
    private void nestedQuantifierTest7() {}

    //@ ensures (\forall int i; i >= 5 && i < 10; (\forall int j; j >= 0 && j < 2; (\exists int k; k >= 2 && k < 5; i > k && k > j)));
    @Verifyable
    private void nestedQuantifierTest8() {}

    //@ ensures (\forall int i; i >= 5 && i < 10; (\forall int j; j >= 0 && j < 2; (\exists int k; k >= 6 && k < 10; i > k && k > j)));
    @Fails
    private void nestedQuantifierTest9() {}

    //@ ensures (\exists int i; i >= 0 && i < 10; (\exists int j; j >= 0 && j < 10; (\forall int k; k >= 2 && k < 5; i > k && k > j)));
    @Verifyable
    private void nestedQuantifierTest10() {}

    //@ ensures (\exists int i; i >= 5 && i < 10; (\exists int j; j >= 0 && j < 2; (\forall int k; k >= 6 && k < 10; i > k && k > j)));
    @Fails
    private void nestedQuantifierTest11() {}

    //@ requires (\exists int i; i >= 0 && i < 10; i > 5);
    //@ ensures false;
    @Fails
    private void requiresTest() {
    }

    //@ requires false;
    //@ ensures false;
    @Verifyable
    private void requiresTest2(int j) {
    }

    //@ requires j > 10;
    //@ requires (\exists int i; i >= 0 && i < 10; i > j);
    //@ ensures false;
    @Verifyable
    private void requiresTest1(int j) {
    }

    //@ requires (\forall int i; i >= 0 && i < 10; \exists int j; j >= 0 && j <= 10; j > i);
    //@ ensures false;
    @Fails
    private void requiresTest3() {
    }

    //@ requires (\forall int i; i >= 0 && i < 10; \exists int j; j >= 0 && j < 10; j > i);
    //@ ensures false;
    @Verifyable
    private void requiresTest4() {
    }

    //@ requires (\exists int i; i >= 0 && i < 10; \exists int j; j >= 0 && j <= 10; j > i);
    //@ ensures false;
    @Fails
    private void requiresTest5() {
    }

    //@ requires (\exists int i; i >= 0 && i < 0; \exists int j; j >= 0 && j < 10; j > i);
    //@ ensures false;
    @Verifyable
    private void requiresTest6() {
    }

    //@ requires (\forall int i; i >= 0 && i < 10; \forall int j; j >= 10 && j <= 10; j > i);
    //@ ensures false;
    @Fails
    private void requiresTest7() {
    }

    //@ requires (\forall int i; i >= 0 && i < 10; \forall int j; j >= 0 && j < 10; j > i);
    //@ ensures false;
    @Verifyable
    private void requiresTest8() {
    }

    //@ ensures !(true && (\exists int i; i >= 0 && i < 5; i > 3));
    @Fails
    private void negatedTest() {
    }

    //@ ensures (\forall int i; i >= 0 && i < 5; i > -1) || (\forall int j; j >= 0 && j < 5; j > 0);
    @Verifyable
    private void binaryTest() {
    }

    //@ ensures (\forall int i; i >= 0 && i < 5; i > -1) && (\forall int j; j >= 0 && j < 5; j > 0);
    @Fails
    private void binaryTest1() {
    }

    //@ ensures (\exists int i; i >= 0 && i < 5; i > -1) || (\exists int j; j >= 0 && j < 5; j > 0);
    @Verifyable
    private void binaryTest2() {
    }

    //@ ensures (\exists int i; i >= 0 && i < 5; i > -1) && (\exists int j; j >= 0 && j < 5; j > 6);
    @Fails
    private void binaryTest3() {
    }

    //@ ensures true || (\exists int i; 0 <= i && i < 1; 1/0 == 0);
    @Verifyable
    private void shortcutTest() {
    }

    //@ ensures false && (\exists int i; 0 <= i && i < 1; 1/0 == 0);
    @Fails
    private void shortcutTest1() {
    }

    //@ ensures false || (\exists int i; 0 <= i && i < 1; 1/0 == 0);
    @Fails
    private void shortcutTest2() {
    }

    //@ ensures true && (\exists int i; 0 <= i && i < 1; 1/0 == 0);
    @Fails
    private void shortcutTest3() {
    }
}
