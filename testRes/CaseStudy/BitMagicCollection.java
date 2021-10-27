package CaseStudy;

/**
 * Created by jklamroth on 2/1/19.
 */
class BitMagicCollection {
    //greatest Power of 2 less or equal to x
    /*@ requires x > 0;
      @ ensures !(\exists int j; j > 0 && j < 33; 1 << j < x && 1 << j > \result);
     */
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
    /*@ requires x > 0;
      @ ensures (\forall int i; 0 <= i < 32; (\exists int j; i <= j < i + \result + 1; (x & (1 << j)) == 0));
      @ ensures (\exists int i; 0 <= i < 32; (\forall int j; i <= j < i + \result; (x & (1 << j)) != 0));
      @*/
    public static int findMax1String(int x) {
        int k;
        for(k = 0; x != 0; k++) {
            x = x & 2*x;
        }
        return k;
    }
}
