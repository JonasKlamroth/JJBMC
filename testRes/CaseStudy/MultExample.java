package CaseStudy;

/**
 * Created by jklamroth on 2/1/19.
 */
public class MultExample {
    /*@
      @ requires 0 <= x1 && 0 <= x2;
      @ requires x1 < 256 && x2 < 256;
      @ ensures \result == x1 * x2;
      @ assignable \nothing;
      @*/
    public static int mult(int x1, int x2) {
        int res = 0;
        //@ loop_invariant res == i * x2;
        //@ loop_invariant 0 <= i && i <= x1;
        //@ loop_modifies res;
        //@ decreases (x1 - i) + 1;
        for (int i = 0; i < x1; ++i) {
            res += x2;
        }
        return res;
    }

}
