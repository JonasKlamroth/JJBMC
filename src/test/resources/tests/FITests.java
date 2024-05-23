package tests;

import jjbmc.Verifyable;
import jjbmc.Fails;

public class FITests {

    //@ ensures \result == 0;
    @Verifyable
    public int inlineOptionTest1() {
        return inlineOptionTestCallee1(1);
    }

    //@ requires i > 0;
    //@ ensures \result == 1;
    //@ assignable \nothing;
    @Fails
    public int inlineOptionTestCallee1(int i) {
        return i - 1;
    }

    //@ ensures \result == 0;
    @Verifyable
    public int inlineOptionTest2() {
        return inlineOptionTestCallee2(1);
    }

    //@ requires i < 0;
    //@ ensures \result == 1;
    //@ assignable \nothing;
    @Fails
    public int inlineOptionTestCallee2(int i) {
        return i - 1;
    }
}