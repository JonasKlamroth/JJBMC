//package openjml.demo;

import java.io.FileNotFoundException;

public class Paths {

    //@   requires min <= max;
    //@   requires i < min;
    //@   ensures \result == min;
    public int clip(int i, int max, int min) {
        if (i < min) return min;
        if (i > max) return max;
        return i;
    }

    //@ requires min <= max;
    //@ requires i > max;
    //@ ensures \result == max;
    public int clip1(int i, int max, int min) {
        if (i < min) return min;
        if (i > max) return max;
        return i;
    }

    //@ requires min <= max;
    //@ requires i >= min && i <= max;
    //@ ensures \result == i;
    public int clip2(int i, int max, int min) {
        if (i < min) return min;
        if (i > max) return max;
        return i;
    }

//    public void multipleErrors(int i) {
//        if (i == 0) {
//            //@ assert i > 0;
//        } else {
//            //@ assert i > 0;
//        }
//    }

//    public void lotsOfPaths(int i) {
//        int k = 0; int j = 1;
//        switch (i) {
//            default: k = i; break;
//            case 1: k = 1; break;
//            case 2: k = 2; break;
//            case 3: k = 3; break;
//        }
//        //@ assert i == k;
//
//        try {
//            throw new Exception();
//            //throw new RuntimeException();
//            //throw new FileNotFoundException();
//            //throw new NullPointerException();
//        } catch (RuntimeException e) {
//            j = 2;
//        } catch (Exception e) {
//            j = 3;
//        } finally {
//            i += k;
//        }
//    }

    public void testConstant(/*@ nullable */Object o) {
        o = this;
        //@ assert o == this;
        o = new RuntimeException();
        ////@ assert \typeof(o) <: \type(Exception);
        o = null;
        //@ assert o == null;
    }

}