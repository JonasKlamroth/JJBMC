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
    private int privInt;
    TmpTest[] objects;

    //@ requires t2 != null && t2.objects != null && t2.objects.length >= 1 && t2.objects[2] != null;
    //@ assignable t2.objects[0..1].t2;
    @Fails
    private void assignableTest15() {
        t2.objects[2].t2 = new TmpTest();
    }

}
