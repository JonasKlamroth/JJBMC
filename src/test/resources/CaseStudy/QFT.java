public class QFT {

    public QFT() {
        super();
    }

    /*@ non_null */
    private static final float[][] R4i = new float[][]{new float[]{0.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, 0.70710677F}};
    /*@ non_null */
    private static final float[][] R4 = new float[][]{new float[]{1.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, 1.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, 1.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, 0.70710677F}};
    /*@ non_null */
    private static final float[][] R2i = new float[][]{new float[]{0.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, 1.0F}};
    /*@ non_null */
    private static final float[][] R2 = new float[][]{new float[]{1.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, 1.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, 1.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, 0.0F}};
    /*@
      requires qstate != null && qstatei != null && qstate.length == 8 && qstatei.length == 8;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public void qft(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7]};
        q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[1], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[1], 0.70710677F * q_state_0[2] + 0.70710677F * q_state_0[3], 0.70710677F * q_state_0[2] + -0.70710677F * q_state_0[3], 0.70710677F * q_state_0[4] + 0.70710677F * q_state_0[5], 0.70710677F * q_state_0[4] + -0.70710677F * q_state_0[5], 0.70710677F * q_state_0[6] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[6] + -0.70710677F * q_state_0[7]};
        q_state_1 = new float[]{0.70710677F * q_state_1[0] + 0.70710677F * q_state_1[1], 0.70710677F * q_state_1[0] + -0.70710677F * q_state_1[1], 0.70710677F * q_state_1[2] + 0.70710677F * q_state_1[3], 0.70710677F * q_state_1[2] + -0.70710677F * q_state_1[3], 0.70710677F * q_state_1[4] + 0.70710677F * q_state_1[5], 0.70710677F * q_state_1[4] + -0.70710677F * q_state_1[5], 0.70710677F * q_state_1[6] + 0.70710677F * q_state_1[7], 0.70710677F * q_state_1[6] + -0.70710677F * q_state_1[7]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], -1.0F * q_state_1[3], q_state_0[4], q_state_0[5], q_state_0[6], -1.0F * q_state_1[7]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_0[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_0[7]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[2], q_state_0[1], q_state_0[3], q_state_0[4], q_state_0[6], q_state_0[5], q_state_0[7]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[2], q_state_1[1], q_state_1[3], q_state_1[4], q_state_1[6], q_state_1[5], q_state_1[7]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], 0.70710677F * q_state_0[3] + -0.70710677F * q_state_1[3], q_state_0[4], q_state_0[5], q_state_0[6], 0.70710677F * q_state_0[7] + -0.70710677F * q_state_1[7]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], 0.70710677F * q_state_1[3] + 0.70710677F * q_state_0[3], q_state_1[4], q_state_1[5], q_state_1[6], 0.70710677F * q_state_1[7] + 0.70710677F * q_state_0[7]};
        q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[4], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[5], 0.70710677F * q_state_0[2] + 0.70710677F * q_state_0[6], 0.70710677F * q_state_0[3] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[4], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[5], 0.70710677F * q_state_0[2] + -0.70710677F * q_state_0[6], 0.70710677F * q_state_0[3] + -0.70710677F * q_state_0[7]};
        q_state_1 = new float[]{0.70710677F * q_state_1[0] + 0.70710677F * q_state_1[4], 0.70710677F * q_state_1[1] + 0.70710677F * q_state_1[5], 0.70710677F * q_state_1[2] + 0.70710677F * q_state_1[6], 0.70710677F * q_state_1[3] + 0.70710677F * q_state_1[7], 0.70710677F * q_state_1[0] + -0.70710677F * q_state_1[4], 0.70710677F * q_state_1[1] + -0.70710677F * q_state_1[5], 0.70710677F * q_state_1[2] + -0.70710677F * q_state_1[6], 0.70710677F * q_state_1[3] + -0.70710677F * q_state_1[7]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], -1.0F * q_state_1[6], -1.0F * q_state_1[7]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_0[6], q_state_0[7]};
        q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[3], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[3], 0.70710677F * q_state_0[4] + 0.70710677F * q_state_0[6], 0.70710677F * q_state_0[5] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[4] + -0.70710677F * q_state_0[6], 0.70710677F * q_state_0[5] + -0.70710677F * q_state_0[7]};
        q_state_1 = new float[]{0.70710677F * q_state_1[0] + 0.70710677F * q_state_1[2], 0.70710677F * q_state_1[1] + 0.70710677F * q_state_1[3], 0.70710677F * q_state_1[0] + -0.70710677F * q_state_1[2], 0.70710677F * q_state_1[1] + -0.70710677F * q_state_1[3], 0.70710677F * q_state_1[4] + 0.70710677F * q_state_1[6], 0.70710677F * q_state_1[5] + 0.70710677F * q_state_1[7], 0.70710677F * q_state_1[4] + -0.70710677F * q_state_1[6], 0.70710677F * q_state_1[5] + -0.70710677F * q_state_1[7]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[2], q_state_0[1], q_state_0[3], q_state_0[4], q_state_0[6], q_state_0[5], q_state_0[7]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[2], q_state_1[1], q_state_1[3], q_state_1[4], q_state_1[6], q_state_1[5], q_state_1[7]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[4], q_state_0[2], q_state_0[6], q_state_0[1], q_state_0[5], q_state_0[3], q_state_0[7]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[4], q_state_1[2], q_state_1[6], q_state_1[1], q_state_1[5], q_state_1[3], q_state_1[7]};
        boolean $$_tmp_measureVar1;
        float m1 = (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4]) * (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4]) + (q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5]) * (q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5]) + (q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6]) * (q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6]) + (q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7]) * (q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7]);
        float m2 = (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) * (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) + (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) * (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) + (q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) * (q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) + (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) * (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]);
        if (m1 > m2) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7]};
            $$_tmp_measureVar1 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar1 = false;
        }
        boolean b0 = $$_tmp_measureVar1;
        assert b0 = false;
        boolean $$_tmp_measureVar2;
        if ((q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) * (q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) + (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) * (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) + (q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6]) * (q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6]) + (q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7]) * (q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7]) > (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) * (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) + (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) * (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) + (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4]) * (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4]) + (q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5]) * (q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5])) {
            q_state_0 = new float[]{0.0F, 0.0F, q_state_0[2], q_state_0[3], 0.0F, 0.0F, q_state_0[6], q_state_0[7]};
            q_state_1 = new float[]{0.0F, 0.0F, q_state_1[2], q_state_1[3], 0.0F, 0.0F, q_state_1[6], q_state_1[7]};
            $$_tmp_measureVar2 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], 0.0F, 0.0F, q_state_0[4], q_state_0[5], 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], 0.0F, 0.0F, q_state_1[4], q_state_1[5], 0.0F, 0.0F};
            $$_tmp_measureVar2 = false;
        }
        boolean b1 = $$_tmp_measureVar2;
        assert b1 = false;
        boolean $$_tmp_measureVar3;
        if ((q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) * (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) + (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) * (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) + (q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5]) * (q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5]) + (q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7]) * (q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7]) > (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) * (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) + (q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) * (q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) + (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4]) * (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4]) + (q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6]) * (q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6])) {
            q_state_0 = new float[]{0.0F, q_state_0[1], 0.0F, q_state_0[3], 0.0F, q_state_0[5], 0.0F, q_state_0[7]};
            q_state_1 = new float[]{0.0F, q_state_1[1], 0.0F, q_state_1[3], 0.0F, q_state_1[5], 0.0F, q_state_1[7]};
            $$_tmp_measureVar3 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], 0.0F, q_state_0[2], 0.0F, q_state_0[4], 0.0F, q_state_0[6], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F, q_state_1[2], 0.0F, q_state_1[4], 0.0F, q_state_1[6], 0.0F};
            $$_tmp_measureVar3 = false;
        }
        boolean b2 = $$_tmp_measureVar3;
        assert b2 = false;
    }
}
