import org.cprover.CProver;


public class BB84 {

    public BB84() {
        super();
    }

    public boolean generateKeyBit(boolean a, boolean b, boolean bprime) {
        float[] q0 = new float[]{1.0F, 0.0F};
        float[] q1 = new float[]{0.0F, 0.0F};
        if (a) {
            q0 = new float[]{0.0F, 1.0F};
            q1 = new float[]{0.0F, 0.0F};
        }
        if (b) {
            q0 = new float[]{0.70710677F * q0[0] + 0.70710677F * q0[1], 0.70710677F * q0[0] + -0.70710677F * q0[1]};
            q1 = new float[]{0.70710677F * q1[0] + 0.70710677F * q1[1], 0.70710677F * q1[0] + -0.70710677F * q1[1]};
        }
        if (bprime) {
            q0 = new float[]{0.70710677F * q0[0] + 0.70710677F * q0[1], 0.70710677F * q0[0] + -0.70710677F * q0[1]};
            q1 = new float[]{0.70710677F * q1[0] + 0.70710677F * q1[1], 0.70710677F * q1[0] + -0.70710677F * q1[1]};
        }
        boolean $$_tmp_measureVar1;
        if (CProver.nondetBoolean()) {
            if (true && q0[0] == 0.0F && q1[0] == 0.0F) CProver.assume(false);
            q0 = new float[]{q0[0], 0.0F};
            q1 = new float[]{q1[0], 0.0F};
            $$_tmp_measureVar1 = false;
        } else {
            if (true && q0[1] == 0.0F && q1[1] == 0.0F) CProver.assume(false);
            q0 = new float[]{0.0F, q0[1]};
            q1 = new float[]{0.0F, q1[1]};
            $$_tmp_measureVar1 = true;
        }
        boolean aprime = $$_tmp_measureVar1;
        assert b != bprime || a == aprime;
        return aprime;
    }

    /*@
      requires a != null && b != null && bprime != null;
      requires a.length == b.length && b.length == bprime.length;
      ensures \result != null && \result.length <= a.length;
   */
    public boolean[] generateKeyBits(/*@ non_null */
            boolean[] a, /*@ non_null */
            boolean[] b, /*@ non_null */
            boolean[] bprime) {
        /*@ non_null */
        boolean[] res = new boolean[a.length];
        int idx = 0;
        for (int i = 0; i < a.length; ++i) {
            boolean bit = generateKeyBit(a[i], b[i], bprime[i]);
            if (b[i] == bprime[i]) {
                res[idx] = bit;
                idx++;
            }
        }
        /*@ non_null */
        boolean[] bits = new boolean[idx];
        for (int i = 0; i < bits.length; ++i) {
            bits[i] = res[i];
        }
        return bits;
    }
}
