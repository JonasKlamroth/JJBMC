/**
 * Created by jklamroth on 12/18/18.
 */
public class NormalBigInt {
    int[] result;

    final static long LONG_MASK = 0xffffffffL;

    // returns the value of the input integer as if it was unsigned
    /*@ ensures value == 0 ==> \result == 0;
	  @ ensures value != 0 ==> \result > 0;
      @ ensures value > 0 ==> \result == value;
      @ ensures value < 0 ==> \result == value + 0x100000000L;
      @ ensures \result >= 0;
      @ ensures \result < 0x100000000L;
      @*/
    public static long toUnsigned(int value) {
        return (long)value & 0xffffffffL;
    }

/* left out:
    @ ensures (\forall int i; value != i ==> \result != toUnsigned(i));		// injective function -> proven in KeY
    @ accessible \nothing;
      @ public static helper model long toUnsigned(int value) {
      @     return (long)value & 0xffffffffL;
        @ }

        */
/*
    public static void main(int value, int other) {
        long result = toUnsigned(value);
        long otherRes = toUnsigned(other);

        assert value != 0 || result == 0;
        assert value == 0 || result > 0;
        assert value <= 0 || result == value;
        assert value >= 0 || result == value + 0x100000000L;
        assert result >= 0;
        assert result < 0x100000000L;
        if (value != other) {
            assert result != otherRes;
        }
    }*/

    /*@ requires sum >= 0;
      @ ensures \result == sum / 0x100000000L;
      @*/
    private static long shiftLeftBy32Bits(long sum) {
        long sum1 = sum;
        return sum >>> 32;
    }

    /*@ requires i >= 0;
      @ ensures \result == i;
      @*/
    private static long andLongMask(int i) {
        return i & LONG_MASK;
    }
}
