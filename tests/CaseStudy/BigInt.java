package CaseStudy;

import TestAnnotations.Verifyable;

/**
 * Created by jklamroth on 12/18/18.
 */
public class BigInt {
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
    @Verifyable
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

    /*@ requires y != null && y.length < 5 && x != null && x.length < 5;
      @ requires xIndex >= 0 && xIndex < y.length && yIndex >= 0 && yIndex < y.length;
      @ requires x.length - xIndex == y.length - yIndex;
      @ ensures result[xIndex - 1] == (((long)x[xIndex - 1] & 0xffffffffL)
      @ 	+ ((long)y[yIndex - 1] & 0xffffffffL) + (sum / 0x100000000L)) % 0x100000000L;
      @ assignable result[xIndex - 1];
      @*/
    @Verifyable
    public void block(int[] x, int[] y, int xIndex, int yIndex, long sum, int[] result) {
            sum = (x[--xIndex] & LONG_MASK) +
                    (y[--yIndex] & LONG_MASK) + (sum >>> 32);
            result[xIndex] = (int)sum;
    }
}
