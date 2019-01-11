package CaseStudy;

import TestAnnotations.Fails;
import TestAnnotations.Verifyable;
import org.cprover.CProver;

/**
 * Created by jklamroth on 12/18/18.
 */
public class TmpTest {
    int[] arr;
    TmpTest t2;
    public int pubInt;
    private int privInt;
    TmpTest[] objects;

    //@ requires t2 != null && t2.objects != null && t2.objects.length >= 1 && t2.objects[0] != null;
    //@ assignable t2.objects[0..1].t2;
    @Verifyable
    private void assignableTest14() {
        t2.objects[0].t2 = new TmpTest();
    }

    //@ requires t2 != null && t2.objects != null && t2.objects.length >= 1 && t2.objects[2] != null;
    //@ assignable t2.objects[0..1].t2;
    @Fails
    private void assignableTest15() {
        t2.objects[2].t2 = new TmpTest();
    }

    /*@ assignable t2.*;
      @ */
    @Fails
    private void assignalbeTest5(TmpTest t3) {
        t3 = new TmpTest();
        t3.pubInt = 5;
        t3.t2 = new TmpTest();
        t3.t2.pubInt = 10;
        t3.arr = new int[10];
        t3.arr[5] = 10;
    }

    /*@ requires t2 != null;
      @ assignable t2.*;
      @ */
    @Verifyable
    private void assignalbeTest51(TmpTest t3) {
        t3 = this.t2;
        t3.pubInt = 5;
        t3.t2 = new TmpTest();
        t3.arr = new int[10];
        t3.arr[5] = 10;
    }

}
