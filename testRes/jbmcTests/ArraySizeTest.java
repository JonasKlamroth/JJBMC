//This is an example which works if --max-nondet-array-length N is specified and
//N is equal or more than arraySize and fails otherwise
public class ArraySizeTest {
    public int[] p;
    public final int arraySize = 7;

    //@ requires p != null && p.length == arraySize;
    //@ ensures (\forall int i; i >= 0 && i < p.length; p[i] == 3);
    public void test() {
        for(int i = 0; i < arraySize; ++i) {
            p[i] = 3;
        }
        p[arraySize - 1] = 4;
    }
}