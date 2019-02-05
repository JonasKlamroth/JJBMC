package CaseStudy;

import TestAnnotations.Unwind;
import TestAnnotations.Verifyable;

/**
 * Created by jklamroth on 2/1/19.
 */
class BitMagicCollection {
    //greatest Power of 2 less or equal to x
    /*@ requires x > 0;
      @ ensures !(\exists int j; j > 0 && j < 33; Math.pow(2, j) < x && Math.pow(2, j) > \result);
     */
    @Verifyable
    @Unwind(number = 35)
    public static int flp2(int x) {
        x = x | (x >> 1);
        x = x | (x >> 2);
        x = x | (x >> 4);
        x = x | (x >> 8);
        x = x | (x >> 16);
        return x - (x >> 1);
    }

    //find longest string of 1´s
    //for x > 0
    public static int findMax1String(int x) {
        int k;
        for(k = 0; x != 0; k++) {
            x = x & 2*x;
        }
        return k;

    }
}
