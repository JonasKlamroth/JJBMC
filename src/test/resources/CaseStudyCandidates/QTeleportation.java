public class QTeleportation {

    public QTeleportation() {
        super();
    }

    /*@ pure */
    public static boolean isClose(float val, float to) {
        float roundError = 1.0E-5F;
        return val < to + roundError && val > to - roundError;
    }
    /*@
      requires isClose(a * a + b * b, 1.0F);
      ensures a <= b == \result;
   */

    public static boolean generationTest(float a, float b, boolean $$_tmp_measureParam0, boolean $$_tmp_measureParam1) {
        /*@ non_null */
        float[] qStates_r = new float[]{a, b, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
        /*@ non_null */
        float[] qStates_c = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
        float[] q_state_0 = new float[]{qStates_r[0], qStates_r[1], qStates_r[2], qStates_r[3], qStates_r[4], qStates_r[5], qStates_r[6], qStates_r[7]};
        float[] q_state_1 = new float[]{qStates_c[0], qStates_c[1], qStates_c[2], qStates_c[3], qStates_c[4], qStates_c[5], qStates_c[6], qStates_c[7]};
        q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[3], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[3], 0.70710677F * q_state_0[4] + 0.70710677F * q_state_0[6], 0.70710677F * q_state_0[5] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[4] + -0.70710677F * q_state_0[6], 0.70710677F * q_state_0[5] + -0.70710677F * q_state_0[7]};
        q_state_1 = new float[]{0.70710677F * q_state_1[0] + 0.70710677F * q_state_1[2], 0.70710677F * q_state_1[1] + 0.70710677F * q_state_1[3], 0.70710677F * q_state_1[0] + -0.70710677F * q_state_1[2], 0.70710677F * q_state_1[1] + -0.70710677F * q_state_1[3], 0.70710677F * q_state_1[4] + 0.70710677F * q_state_1[6], 0.70710677F * q_state_1[5] + 0.70710677F * q_state_1[7], 0.70710677F * q_state_1[4] + -0.70710677F * q_state_1[6], 0.70710677F * q_state_1[5] + -0.70710677F * q_state_1[7]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[3], q_state_0[2], q_state_0[4], q_state_0[5], q_state_0[7], q_state_0[6]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[3], q_state_1[2], q_state_1[4], q_state_1[5], q_state_1[7], q_state_1[6]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[6], q_state_0[7], q_state_0[4], q_state_0[5]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[6], q_state_1[7], q_state_1[4], q_state_1[5]};
        q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[4], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[5], 0.70710677F * q_state_0[2] + 0.70710677F * q_state_0[6], 0.70710677F * q_state_0[3] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[4], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[5], 0.70710677F * q_state_0[2] + -0.70710677F * q_state_0[6], 0.70710677F * q_state_0[3] + -0.70710677F * q_state_0[7]};
        q_state_1 = new float[]{0.70710677F * q_state_1[0] + 0.70710677F * q_state_1[4], 0.70710677F * q_state_1[1] + 0.70710677F * q_state_1[5], 0.70710677F * q_state_1[2] + 0.70710677F * q_state_1[6], 0.70710677F * q_state_1[3] + 0.70710677F * q_state_1[7], 0.70710677F * q_state_1[0] + -0.70710677F * q_state_1[4], 0.70710677F * q_state_1[1] + -0.70710677F * q_state_1[5], 0.70710677F * q_state_1[2] + -0.70710677F * q_state_1[6], 0.70710677F * q_state_1[3] + -0.70710677F * q_state_1[7]};
        boolean $$_tmp_measureVar1;
        if ($$_tmp_measureParam0) {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar1 = false;
        } else {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7]};
            $$_tmp_measureVar1 = true;
        }
        boolean b0 = $$_tmp_measureVar1;
        boolean $$_tmp_measureVar2;
        if ($$_tmp_measureParam1) {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], 0.0F, 0.0F, q_state_0[4], q_state_0[5], 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], 0.0F, 0.0F, q_state_1[4], q_state_1[5], 0.0F, 0.0F};
            $$_tmp_measureVar2 = false;
        } else {
            q_state_0 = new float[]{0.0F, 0.0F, q_state_0[2], q_state_0[3], 0.0F, 0.0F, q_state_0[6], q_state_0[7]};
            q_state_1 = new float[]{0.0F, 0.0F, q_state_1[2], q_state_1[3], 0.0F, 0.0F, q_state_1[6], q_state_1[7]};
            $$_tmp_measureVar2 = true;
        }
        boolean b1 = $$_tmp_measureVar2;
        if (b1) {
            q_state_0 = new float[]{q_state_0[1], q_state_0[0], q_state_0[3], q_state_0[2], q_state_0[5], q_state_0[4], q_state_0[7], q_state_0[6]};
            q_state_1 = new float[]{q_state_1[1], q_state_1[0], q_state_1[3], q_state_1[2], q_state_1[5], q_state_1[4], q_state_1[7], q_state_1[6]};
        }
        if (b0) {
            q_state_0 = new float[]{q_state_0[0], -1.0F * q_state_0[1], q_state_0[2], -1.0F * q_state_0[3], q_state_0[4], -1.0F * q_state_0[5], q_state_0[6], -1.0F * q_state_0[7]};
            q_state_1 = new float[]{q_state_1[0], -1.0F * q_state_1[1], q_state_1[2], -1.0F * q_state_1[3], q_state_1[4], -1.0F * q_state_1[5], q_state_1[6], -1.0F * q_state_1[7]};
        }
        boolean $$_tmp_measureVar3;
        if (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6]) {
            q_state_0 = new float[]{0.0F, q_state_0[1], 0.0F, q_state_0[3], 0.0F, q_state_0[5], 0.0F, q_state_0[7]};
            q_state_1 = new float[]{0.0F, q_state_1[1], 0.0F, q_state_1[3], 0.0F, q_state_1[5], 0.0F, q_state_1[7]};
            $$_tmp_measureVar3 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], 0.0F, q_state_0[2], 0.0F, q_state_0[4], 0.0F, q_state_0[6], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F, q_state_1[2], 0.0F, q_state_1[4], 0.0F, q_state_1[6], 0.0F};
            $$_tmp_measureVar3 = false;
        }
        return $$_tmp_measureVar3;
    }
}
