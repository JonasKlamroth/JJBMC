package CaseStudy;

/**
 * Created by jklamroth on 12/18/18.
 */
public class TmpTest {
    class IntObject {
        public int i = 0;
    }
    private int privInt = 0;
    private TmpTest tt = null;
    public int pubInt = 0;
    int[] table;
    Object[] otable;
    IntObject[] iotable;

    //@ requires table != null && table.length == 3;
    //@ requires arg != 0;
    //@ requires (\exists int i; 0 <= i < table.length; table[i] == arg);
    private void testIntArrayAssume(int arg) {
        assert false;
    }


    //@ requires otable != null && otable.length == 3;
    //@ requires (\exists int i; 0 <= i < otable.length; otable[i] == arg);
    private void testObjArrayAssume2(Object arg) {
        assert false;
    }

    //@ requires otable != null && otable.length == 3;
    //@ requires arg != null;
    //@ requires (\exists int i; 0 <= i < otable.length; otable[i] == arg);
    private void testObjArrayAssume(Object arg) {
        assert false;
    }

    //@ requires otable != null && otable.length == 3;
    //@ ensures (\forall int i; 0 <= i < otable.length; otable[i] == null);
    private void testObjArrayAssume3(Object arg) {
        Object o0 = otable[0];
        Object o1 = otable[1];
        Object o2 = otable[2];
    }

    //@ requires iotable != null && iotable.length == 3;
    //@ requires arg != null;
    //@ requires (\exists int i; 0 <= i < iotable.length; iotable[i].i == arg.i);
    private void testObjArrayAssume3(IntObject arg) {
        assert false;
    }

    //@ requires iotable != null && iotable.length == 3;
    //@ requires arg != null;
    //@ requires (\exists int i; 0 <= i < iotable.length; iotable[i] == arg);
    private void testObjArrayAssume4(IntObject arg) {
        assert false;
    }

    //@ requires o1 == o2 && o1 != null;
    private void aliasTest(Object o1, Object o2) {
        assert false;
    }
}
