package tests;

import TestAnnotations.Fails;
import TestAnnotations.Unwind;
import TestAnnotations.Verifyable;

/**
 * Created by jklamroth on 1/11/19.
 */

class TestSuite {
    private int privInt = 0;
    public int pubInt;
    TestSuite t2;
    TestSuite t3;
    int[] arr;
    TestSuite[] objects;
}

class A { public A a1; }
class B extends A { public B b1; }

public class AssignableTests {
    private int privInt = 0;
    public int pubInt;
    TestSuite t2;
    TestSuite t3;
    int[] arr;
    TestSuite[] objects;
    Object o;
    A a;
    B b;



    /*@ assignable privInt;
      @ */
    @Verifyable
    private void AssignalbeTest() {
        privInt = 0;
    }

    //@ requires b != null;
    //@ assignable b.a1, a;
    @Verifyable
    private void assignableTestInheritance() {
        a = b;
        a.a1 = new A();
    }

    /*@ assignable t2;
      @ */
    @Fails
    private void assignalbeTest1(TestSuite t3) {
        t3 = new TestSuite();
        t3.t2 = new TestSuite();
        privInt = 0;
    }

    /*@ requires arr != null && arr.length > 5;
      @ assignable arr[5];
      @ */
    @Verifyable
    private void assignalbeTest101() {
        this.arr[5] = 3;
    }

    /*@ requires arr != null && arr.length > 5;
      @ assignable this.arr[5];
      @ */
    @Verifyable
    private void assignalbeTest102() {
        arr[5] = 3;
    }

    /*@ requires arr != null && arr.length > 4;
      @ assignable arr[4];
      @ */
    @Fails
    private void assignalbeTest10() {
        arr[1] = 5;
        arr[4] = 3;
    }

    /*@ requires arr != null && arr.length > 4;
      @ assignable arr[4], arr[2];
      @ */
    @Fails
    private void assignalbeTest12() {
        arr[1] = 5;
        arr[4] = 3;
    }

    //@ assignable this.*;
    @Verifyable
    private void asteriskTest1() {
        t2 = new TestSuite();
    }

    //@ assignable this.*;
    @Fails
    private void asteriskTest() {
        t2 = new TestSuite();
        t2.pubInt = 1;
    }

    /*@ requires arr != null && arr.length > 4;
      @ assignable arr[4];
      @ */
    @Verifyable
    private void assignalbeTest103() {
        arr[4] = 3;
    }

    /*@ requires arr != null && arr.length > 4;
      @ assignable arr[4], arr[1..2], arr[3..];
      @ */
    @Verifyable
    private void assignalbeTest11() {
        arr[1] = 5;
        arr[4] = 3;
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

    }

    /*@ requires arr != null && arr.length > 4;
      @ assignable arr[1..], t2, t3;
      @ */
    @Verifyable
    private void assignalbeTest42() {
        arr[1] = 2;
    }

    /*@ requires arr != null && arr.length > 4;
      @ assignable t2, t2, pubInt;
      @ */
    @Fails
    private void assignalbeTest43() {
        arr[1] = 2;
    }

    /*@ requires arr != null && arr.length > 5;
      @ assignable arr[1..3], arr[4..5];
      @ */
    @Verifyable
    private void assignalbeTest43(int arr1[]) {
        arr1[4] = 2;
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


    //@ requires t != null;
    //@ assignable t2.*;
    @TestAnnotations.Fails
    private void assignableTest10(TestSuite t) {
        TestSuite testSuite = new TestSuite();
        testSuite = t;
        testSuite.arr = new int[10];
    }

    //@ requires t2 != null;
    //@ assignable t2.*;
    @Verifyable
    private void assignableTest11() {
        TestSuite testSuite = new TestSuite();
        testSuite = t2;
        testSuite.arr = new int[10];
    }

    //@ requires t2 != null;
    //@ assignable t2.*;
    @Fails
    private void assignableTest111() {
        TestSuite testSuite = new TestSuite();
        testSuite.arr = new int[10];
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

    //@ assignable \nothing;
    @Verifyable
    private void assignableTest16() {
        int i = 0;
        ++i;
        assert i == 1;
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

    //@ assignable \nothing;
    @Fails
    private void assignableTest17() {
        TestSuite t2 = new TestSuite();
        t2 = new TestSuite();
        this.t2 = new TestSuite();
    }

    //@ assignable \nothing;
    @Verifyable
    private void assignableTest171() {
        TestSuite t2 = new TestSuite();
        t2 = new TestSuite();
    }

    //@ assignable t2;
    @Verifyable
    private void assignableTest172() {
        TestSuite t2 = new TestSuite();
        t2 = new TestSuite();
    }

    //@ requires t2 != null;
    //@ assignable t2;
    @Fails
    private void assignableTest173() {
        TestSuite t2 = this.t2;
        t2.t2 = new TestSuite();
    }

    //@ requires t2 != null;
    //@ assignable t2.t2;
    @Fails
    //i think this is theoretically wrong but its a sound overapproximation?
    private void assignableTest174() {
        TestSuite t2 = new TestSuite();
        t2.t2 = new TestSuite();
    }

    //@ requires t2 != null;
    //@ assignable t2.t2;
    @Verifyable
    private void assignableTest175() {
        TestSuite t2 = this.t2;
        t2.t2 = new TestSuite();
    }

    //@ assignable \nothing;
    @Verifyable
    private void assignableTest176(TestSuite t) {
        t = new TestSuite();
    }

    //@ requires t != null;
    //@ assignable t3, t2;
    @Verifyable
    private void assignableTest178(TestSuite t) {
        t2 = new TestSuite();
    }

    //@ requires t != null;
    //@ assignable \nothing;
    @Fails
    private void assignableTest177(TestSuite t) {
        t.t2 = new TestSuite();
    }

    @Verifyable
    private void assignableTest18() {
        this.t2 = new TestSuite();
    }

    //@ requires privInt == 0;
    //@ ensures privInt == 10;
    @Verifyable
    @Unwind(number = 12)
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

    //@ requires t2 != null && t2.t2 == t2;
    //@ assignable t2;
    @Verifyable
    private void assignableTest29() {
        t2.t2 = new TestSuite();
    }

    //@ ensures \result == 5;
    //@ assignable \nothing;
    private int fakeTest(int i) {
        return 0;
    }

    private int fakeTest() {
        return 56;
    }


    //@ assignable pubInt;
    @Fails
    private void methodInvAss(int i) {
        test();
    }

    //@ assignable arr[2..4];
    @Fails
    private void methodInvAss1(int i) {
        test1();
    }

    //@ requires arr != null && arr.length > 3;
    //@ assignable arr[1..3];
    @Verifyable
    private void methodInvAss2(int i) {
        test1();
    }

    //@ assignable t2;
    @Verifyable
    private void methodInvAss3(int i) {
        test2();
    }

    //@ assignable this.*;
    //@ requires arr != null && arr.length > 3;
    @Verifyable
    private void methodInvAss4(int i) {
        test1();
    }

    //@ assignable t2;
    @Fails
    private void methodInvAss5(int i) {
        test();
    }

    //@ assignable t2;
    @Fails
    private void methodInvAss6(int i) {
        test3();
    }

    //@ assignable arr;
    @Fails
    private void methodInvAss8() {
        this.arr = new int[5];
        test4(this.arr);
    }

    //@ assignable arr;
    @Fails
    private void methodInvAss9() {
        int[] array = new int[3];
        test4(array);
    }

    //@ assignable \nothing;
    @Fails
    private void methodInvAss7() {
        this.arr = new int[5];
        test4(this.arr);
    }


    //@ assignable \everything;
    private void test() {}

    //@ assignable arr[1..3];
    private void test1() {}

    //@ assignable t2;
    private void test2() {}

    //@ assignable objects;
    private void test3() {}

    //@ assignable arr[*];
    private void test4(int[] arr) {}

    //@ requires t2 != null && t3 != null;
    //@ assignable t2, t2.t2;
    @Fails
    private void testOld(){
        t2 = t3;
        t2.t2 = new TestSuite();
    }

    //@ assignable arr;
    @Fails
    private void testArray() {
        this.arr[0] = 0;
    }

    //@ assignable privInt;
    @Verifyable
    private void assignableTest30() {
        privInt = 0;
    }

    //@ requires true;
    //@ assignable is[*];
    @Verifyable
    private void someAssignTest(int[] is) {
    }

    //@ requires is != null;
    //@ requires is.length < 5;
    //@ ensures (\forall int i; 0 <= i < is.length; is[i] == \old(is[i]));
    @Fails
    @Unwind(number = 7)
    private void someCallTest(int[] is) {
        someAssignTest(is);
    }

    //@ requires a != null;
    //@ requires i >= 0 && i < j && j < a.length;
    //@ assignable a[i], a[j];
    private void someAssign(int[] a, int i, int j) {

    }

    //@ requires a != null && a.length == 5;
    //@ requires i >= 0 && i < j && i < a.length;
    //@ assignable a[0..3];
    @Fails
    private void anotherCallTest(int[] a, int i, int j) {
        someAssign(a, 0, 4);
    }
}
