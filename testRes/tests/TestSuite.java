package tests;

import TestAnnotations.Fails;
import TestAnnotations.Unwind;
import TestAnnotations.Verifyable;

/**
 * Created by jklamroth on 9/18/18.
 */
public class TestSuite {
    class UnusedClassForTestingPurpose {}
    private int privInt = 0;
    public int pubInt;
    TestSuite t2;
    TestSuite t3;
    int[] arr;
    TestSuite[] objects;

    //@ requires b1 == false;
    //@ ensures (b1 == true) ==> -1 > 0;
    @Verifyable
    private void normalizeTest5(boolean b1) {

    }

    @Verifyable
    public TestSuite() {}

    //@ ensures pubInt == i;
    @Verifyable
    public TestSuite(int i) {
        this();
        this.pubInt = i;
        setPrivInt(1);
        assert privInt == 1;
    }


    //@ ensures this.t2.pubInt == 10;
    @Verifyable
    private void constructorTest() {
        t2 = new TestSuite(10);
    }

    //@ ensures b1 == (b2 == b3);
    @Fails
    private void normalizeTest7(boolean b1, boolean b2, boolean b3, boolean b4) {

    }
    //@ ensures !(false == true);
    @Verifyable
    private void normalizeTest6() {

    }

    //@ ensures i > 0 ==> i > -1;
    @Verifyable
    private void impliesTest(int i) {
    }

    //@ ensures 1 == 0 <==> true == false;
    @Verifyable
    public void normalizeTest4() {
    }

    //@ requires  i > 0 && i < 10000;
    //@ ensures \result == i + 1;
    //@ assignable \nothing;
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

    //@ ensures \result == 12;
    @Unwind(number = 6)
    @Verifyable
    private int unspecifiedWhileLoop() {
        int sum = 0;
        while(sum < 10) {
            sum += 3;
        }
        return sum;
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
    public void loopTest2() {
        int[] arr = new int[10];
        int i = 0;
        //@ loop_invariant i > -1 && i <= 10;
        //@ loop_invariant (\forall int j; j >= 0 && j < i; arr[j] == j);
        //@ loop_modifies arr[*];
        //@ decreases 11 - i;
        while (i < 10) {
            //@ assume i > 0;
            arr[i] = i;
            i++;
        }
    }

    @Unwind(number = 11)
    @Verifyable
    public void loopTest1() {
        int[] arr = new int[10];
        int i = 0;
        //@ loop_invariant i > -1 && i <= 10;
        //@ loop_invariant (\forall int j; j >= 0 && j < i; arr[j] == j);
        //@ loop_modifies arr[*];
        //@ decreases 11 - i;
        while (i < 10) {
            arr[i] = i;
            i++;
        }
    }

    @Unwind(number = 11)
    @Verifyable
    public void loopTest3() {
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
    @Fails
    public void decreasesTest6() {
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
    @Fails
    public void decreasesTest4() {
        int[] arr = new int[10];
        //@ loop_invariant i > -1 && i <= 10;
        //@ loop_invariant (\forall int j; j >= 0 && j < i; arr[j] == j);
        //@ loop_modifies arr[*];
        //@ decreases 9 - i;
        for(int i = 0; i < 10; ++i) {
            arr[i] = i;
        }
    }

    @Unwind(number = 11)
    @Verifyable
    public void decreasesTest3() {
        int[] arr = new int[10];
        //@ loop_invariant i > -1 && i <= 10;
        //@ loop_invariant (\forall int j; j >= 0 && j < i; arr[j] == j);
        //@ loop_modifies arr[*];
        //@ decreases 10 - i;
        for(int i = 0; i < 10; ++i) {
            arr[i] = i;
        }
    }

    @Unwind(number = 11)
    @Fails
    public void decreasesTest5() {
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

//    @Verifyable
//    private void blockContractTest() {
//        int i = 0;
//        //@ requires i == 0;
//        //@ ensures i == 6;
//        {
//            i = 5;
//            i++;
//        }
//    }
//
//    @Fails
//    private void blockContractTest1() {
//        int i = 0;
//        //@ requires i == 0;
//        //@ ensures i == 7;
//        {
//            i = 5;
//            i++;
//        }
//    }
//
//    @Fails
//    private void blockContractTest2() {
//        int i = 0;
//        //@ requires i == 1;
//        //@ ensures i == 6;
//        {
//            i = 5;
//            i++;
//        }
//    }

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
    private void objectHavocTest() {
        t2 = null;
        calledMethod();
        assert t2 == null;
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

    //@ requires arr != null && arr.length == 4;
    //@ requires (\forall int i; i >= 0 && i < 4; arr[i] == i);
    //@ ensures (\forall int i; i >= 0 && i < 4; arr[i] == i + 1);
    @Unwind(number = 6)
    @Verifyable
    public void havocTest5(int[] arr) {
        for(int i = 0; i < arr.length; ++i) {
            arr[i]++;
        }
    }

    //@ requires arr != null && arr.length == 5;
    //@ requires (\forall int i; i >= 0 && i < 10; arr[i] == i);
    //@ ensures false;
    @Fails
    private void havocTest6() {
    }

    //@ assignable \nothing;
    //@ ensures \result == 5;
    private int fakeTest(int i) {
        return 0;
    }

    private int fakeTest() {
        return 56;
    }

//    //@ ensures (\exists int i; 0 <= i && i < 1; 1/0 == 0);
//    @Fails
//    private void quantifierTest() {
//    }

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

    //@ ensures !true || !false;
    @Verifyable
    private void normalizeTest() {}

    //@ ensures !(!true && !false);
    @Verifyable
    private void normalizeTest1() {}

    //@ ensures true <== true;
    @Verifyable
    private void normalizeTest22() {}

    //@ ensures (!!true) == true;
    @Verifyable
    private void normalizeTest24() {}

    //@ ensures true && true;
    @Verifyable
    private void normalizeTest23() {}

    //@ ensures true <=!=> false;
    @Verifyable
    private void normalizeTest21() {}

    //@ ensures true != false;
    @Verifyable
    private void normalizeTest20() {}

    //@ ensures \result == 1;
    private int calledMethod1() {
        return 1;
    }

    @Verifyable
    private void classMethodCallTest() {
        int res = this.calledMethod1();
        assert res == 1;
    }

    @Verifyable
    private void typeTranslationTest(short s, byte b, double d, float f, long[] l, char[][] c) {}

    //@ ensures pubInt + 5 == \old(pubInt + 5) + c;
    @Verifyable
    private void oldTest1(int c) {
        pubInt += c;
    }

    //@requires arr != null && arr.length > 0;
    //@requires arr[0] != 0;
    @Verifyable
    private void oldTest2() {
        arr[0] = 1;
    }

    //@ ensures pubInt == \old(pubInt) + c;
    @Verifyable
    private void oldTest(int c) {
        pubInt += c;
    }

    //@ ensures pubInt == \old(pubInt) + \old(privInt);
    //@ ensures privInt == \old(privInt + 1);
    @Verifyable
    private void oldTest5(int c) {
        int i = privInt;
        privInt++;
        pubInt += i;
    }

    //@ requires t2 != null;
    //@ ensures t2 == \old(t2);
    @Verifyable
    private void oldTest6() {
        t2.pubInt = 5;
    }

    //@ requires t2 != null;
    //@ ensures t2 == \old(t2);
    @Fails
    private void oldTest7() {
        t2 = new TestSuite();
    }

    //@ requires arr != null;
    //@ requires arr.length < 4;
    //@ ensures (\forall int i; 0 <= i && i < arr.length; arr[i] == \old(arr[i]));
    @Unwind(number = 10)
    @Verifyable
    private void oldTest8() {
    }


    //@ requires arr != null;
    //@ requires arr.length >= 1;
    //@ requires arr.length < 4;
    //@ ensures (\forall int i; 0 <= i && i < arr.length; arr[i] == \old(arr[i]));
    //@ assignable arr[0];
    @Fails
    @Unwind(number = 10)
    private void oldTest9() {
        arr[0] += 1;
    }


    //@ requires arr != null;
    //@ requires arr.length >= 1;
    //@ requires arr.length < 4;
    //@ requires pubInt == 0;
    //@ ensures (\forall int i; 0 <= i && i < \old(arr.length); pubInt == \old(pubInt + arr[i]));
    //@ assignable arr[0];
    @Fails
    @Unwind(number = 10)
    private void oldTest13() {
        arr[0] += 1;
    }

    //@ requires arr != null;
    //@ requires arr.length == 1 && arr[0] == 0;
    //@ requires pubInt == 0;
    //@ ensures (\forall int i; 0 <= i && i < \old(arr.length); pubInt == \old(pubInt + arr[i]));
    //@ assignable arr[0];
    @Verifyable
    @Unwind(number = 10)
    private void oldTest12() {
        arr[0] += 1;
    }

    //@ requires arr != null;
    //@ requires arr.length == 1 && arr[0] == 0;
    //@ requires pubInt == 0;
    //@ ensures (\forall int i; 0 <= i && i < \old(arr.length); pubInt == \old(pubInt + arr[i]));
    //@ assignable pubInt;
    @Fails
    @Unwind(number = 10)
    private void oldTest11() {
        pubInt = 1;
    }

    //no assertions but should compile
    private void testSymbOldTest() {
        oldTest10();
        oldTest11();
        oldTest12();
        oldTest13();
    }

    //@ requires arr != null;
    //@ requires arr.length == 1 && arr[0] == 0;
    //@ requires pubInt == 0;
    //@ ensures (\forall int i; 0 <= i && i < \old(arr.length); pubInt == \old(pubInt + arr[i]));
    //@ assignable arr;
    @Verifyable
    @Unwind(number = 10)
    private void oldTest10() {
        arr = new int[3];
    }

    //@ ensures ((\forall int i; i >= 0 && i < 5; i == 3) ? 5 : 3) == 3;
    @Verifyable
    public void ternaryTest() {
    }

    //@ ensures ((\forall int i; i >= 0 && i < 5; i == 3) ? 5 : 3) != 3;
    @Fails
    public void ternaryTest1() {
    }

    //@ ensures ((\exists int i; i >= 0 && i < 5; i == 3) ? 5 : 3) != 3;
    @Verifyable
    public void ternaryTest2() {
    }

    public void setPrivInt(int i) {
        this.privInt = i;
    }

    /*@
      @ private normal_behaviour
      @ requires i >= 0 && i < 10;
      @ ensures \result == i;
      @ assignable \nothing;
      @ also
      @ private normal_behaviour
      @ requires i < 0 && i > -10;
      @ ensures \result == -1 * i;
      @ assignable \nothing;
      @*/
    @Verifyable
    private int abs(int i) {
        if (i >= 0) {
            return i;
        } else {
            return i * -1;
        }
    }

    /*@
      @ private normal_behaviour
      @ requires i < 0 && i > -10;
      @ ensures \result == i;
      @ assignable \nothing;
      @ also
      @ private normal_behaviour
      @ requires i >= 0 && i < 10;
      @ ensures \result == -1 * i;
      @ assignable \nothing;
      @*/
    @Fails
    private int abs2(int i) {
        if (i >= 0) {
            return i;
        } else {
            return i * -1;
        }
    }

    //@ requires i >= 0 && i < 10;
    //@ ensures \result == i;
    @Verifyable
    private int InvocingAbs(int i) {
        return abs(i);
    }

    //@ requires i < 0 && i > -10;
    //@ ensures \result == -i;
    @Verifyable
    private int InvocingAbs5(int i) {
        return abs(i);
    }

    //@ requires i < 0 && i > -10;
    //@ ensures \result == i;
    @Fails
    private int InvocingAbs2(int i) {
        return abs(i);
    }

    //@ requires i < 0 && i > -10;
    //@ ensures \result == i;
    @Verifyable
    private int InvocingAbs3(int i) {
        return abs2(i);
    }

    //@ requires i >= 0 && i < 10;
    //@ ensures \result == i;
    @Fails
    private int InvocingAbs4(int i) {
        return abs2(i);
    }

    //@ requires arr != null;
    //@ ensures (\forall int i; i >= 2 && i < arr.length; arr[i] == \old(arr[i] + 1));
    @Verifyable
    @Unwind(number = 7)
    private void oldArrayTest() {
        for(int i = 0; i < arr.length; ++i) {
            arr[i]++;
        }
    }

    //@ requires arr != null && arr.length >= 2 && arr.length < 5;
    //@ ensures (\forall int i; i >= 1 && i < arr.length; arr[i] == \old(arr[i] + 1));
    @Verifyable
    @Unwind(number = 7)
    private void oldArrayTest3() {
        int[] b = new int[arr.length];

        /*@ loop_invariant i >= 1 && i <= arr.length && (\forall int j; j >= 1 && j < i; b[j] == arr[j] + 1);
          @ loop_modifies i, b[1..arr.length - 1];
          @ decreases arr.length - i;
         */
        for(int i = 1; i < arr.length; ++i) {
            b[i] = arr[i] + 1;
        }
        arr = b;
    }



    //@ ensures \result == 3;
    //@ assignable \nothing;
    @Verifyable
    private int test1() {
        int res = 0;
        for(int i = 0; i++ < 3; res = inc(res)) {
        }
        return res;
    }

    //@ ensures \result == i + 1;
    //@ assignable \nothing;
    private int inc(int i) {
        return i+1;
    }


    private boolean boolFunct(int i) {
        return true;
    }

    @Verifyable
    public boolean shortcutTest4() {
        if(true && boolFunct(0)) {
            return true;
        }
        return false;
    }


    //@ ensures (\forall int i; i > 0 && i < 4; (\exists int j; j > i + 1 && j < 4; j > i));
    @Fails
    @Unwind(number = 6)
    private void nestedQunts() {
    }


    //@ requires array != null && array.length >= 4;
    //@ ensures (\forall int i; 0 < i < 3; (\forall int j; i < j < 4; \old(array[j]) == array[i]));
    @Fails
    private int oldNestedQuantTest(int[] array) {
        return array[0];
    }


    //@ requires array != null && array.length >= 4;
    //@ ensures \old(array) == array;
    //@ ensures (\forall int i; 0 < i < 3; \old(array)[i] == array[i]);
    @Verifyable
    private int testOldInQuntifier(int[] array) {
        return array[0];
    }

    //@ requires array != null && array.length >= 4;
    //@ ensures \old(array) == array;
    //@ ensures (\forall int i; 0 < i < 3; (\forall int j; i - 1 < j < i + 1; \old(array[j]) == array[i]));
    @Verifyable
    private int testOldInQuntifier2(int[] array) {
        return array[0];
    }

    //@ ensures \result == 3;
    @Verifyable
    private int loopInvModTest2() {
        int i = 0;
        //@ loop_invariant 0 <= i <= 3;
        while(i < 3) {
            i++;
        }
        return i;
    }

    //@ requires privInt == 0;
    //@ ensures privInt == 3;
    @Verifyable
    private void loopInvModTest3() {
        //@ loop_invariant 0 <= privInt <= 3;
        while(privInt < 3) {
            incPrivInt();
        }
    }

    //@ assignable privInt;
    //@ ensures privInt == \old(privInt) + 1;
    @Verifyable
    private void incPrivInt() {
        privInt++;
    }


    //@ ensures false;
    @Fails
    private int loopInvModTest() {
        int i = 0;
        //@ loop_invariant 0 <= i <= 3;
        while(i < 3) {
            i++;
        }
        return i;
    }

    //@ assignable \nothing;
    @Verifyable
    private void loopInvAssTest() {
        int j = 0;
        //@ loop_invariant (\forall int i; 0 < i < 3; i > 0);
        while(j < 0) {
            j = inc(j);
        }
    }


    @Fails
    private void assForLoopTest() {
        int j = 0;
        //@ loop_invariant j <= 1;
        for(int i = 0; i < 3; ++i) {
            j += 1;
        }
    }


    @Fails
    private /*@ pure */ void pureMethod() {
        privInt = 1;
    }

    //@ requires privInt == 0;
    //@ ensures privInt == 0;
    //@ assignable \nothing;
    @Verifyable
    private void testPureSymbMethod() {
        pureMethod();
    }


    //@ requires arr != null && arr.length > 0;
    //@ assignable t3;
    private void EnhancedForTest() {
        for(int i : arr) {
            randomMeth();
        }
    }

    //@ assignable t2;
    private void randomMeth() {
    }

}
