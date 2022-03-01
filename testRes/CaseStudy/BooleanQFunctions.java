

public class BooleanQFunctions {

    public BooleanQFunctions() {
        super();
    }
    /*@
      ensures \result == !(a || b);
   */

    public static boolean nor(boolean a, boolean b) {
        float[] q_state_0 = new float[]{1.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
        float[] q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
        if (a) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 1.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
        }
        if (b) {
            q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11]};
            q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11]};
        }
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[14], q_state_0[15], q_state_0[12], q_state_0[13]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[14], q_state_1[15], q_state_1[12], q_state_1[13]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[8], q_state_0[9], q_state_0[4], q_state_0[5], q_state_0[12], q_state_0[13], q_state_0[2], q_state_0[3], q_state_0[10], q_state_0[11], q_state_0[6], q_state_0[7], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[8], q_state_1[9], q_state_1[4], q_state_1[5], q_state_1[12], q_state_1[13], q_state_1[2], q_state_1[3], q_state_1[10], q_state_1[11], q_state_1[6], q_state_1[7], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[8], q_state_0[9], q_state_0[4], q_state_0[5], q_state_0[12], q_state_0[13], q_state_0[2], q_state_0[3], q_state_0[10], q_state_0[11], q_state_0[6], q_state_0[7], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[8], q_state_1[9], q_state_1[4], q_state_1[5], q_state_1[12], q_state_1[13], q_state_1[2], q_state_1[3], q_state_1[10], q_state_1[11], q_state_1[6], q_state_1[7], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[4], q_state_0[2], q_state_0[6], q_state_0[1], q_state_0[5], q_state_0[3], q_state_0[7], q_state_0[8], q_state_0[12], q_state_0[10], q_state_0[14], q_state_0[9], q_state_0[13], q_state_0[11], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[4], q_state_1[2], q_state_1[6], q_state_1[1], q_state_1[5], q_state_1[3], q_state_1[7], q_state_1[8], q_state_1[12], q_state_1[10], q_state_1[14], q_state_1[9], q_state_1[13], q_state_1[11], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[4], q_state_0[2], q_state_0[6], q_state_0[1], q_state_0[5], q_state_0[3], q_state_0[7], q_state_0[8], q_state_0[12], q_state_0[10], q_state_0[14], q_state_0[9], q_state_0[13], q_state_0[11], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[4], q_state_1[2], q_state_1[6], q_state_1[1], q_state_1[5], q_state_1[3], q_state_1[7], q_state_1[8], q_state_1[12], q_state_1[10], q_state_1[14], q_state_1[9], q_state_1[13], q_state_1[11], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[8], q_state_0[9], q_state_0[4], q_state_0[5], q_state_0[12], q_state_0[13], q_state_0[2], q_state_0[3], q_state_0[10], q_state_0[11], q_state_0[6], q_state_0[7], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[8], q_state_1[9], q_state_1[4], q_state_1[5], q_state_1[12], q_state_1[13], q_state_1[2], q_state_1[3], q_state_1[10], q_state_1[11], q_state_1[6], q_state_1[7], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[8], q_state_0[9], q_state_0[4], q_state_0[5], q_state_0[12], q_state_0[13], q_state_0[2], q_state_0[3], q_state_0[10], q_state_0[11], q_state_0[6], q_state_0[7], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[8], q_state_1[9], q_state_1[4], q_state_1[5], q_state_1[12], q_state_1[13], q_state_1[2], q_state_1[3], q_state_1[10], q_state_1[11], q_state_1[6], q_state_1[7], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[14], q_state_0[15], q_state_0[12], q_state_0[13]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[14], q_state_1[15], q_state_1[12], q_state_1[13]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0], q_state_0[3], q_state_0[2], q_state_0[5], q_state_0[4], q_state_0[7], q_state_0[6], q_state_0[9], q_state_0[8], q_state_0[11], q_state_0[10], q_state_0[13], q_state_0[12], q_state_0[15], q_state_0[14]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0], q_state_1[3], q_state_1[2], q_state_1[5], q_state_1[4], q_state_1[7], q_state_1[6], q_state_1[9], q_state_1[8], q_state_1[11], q_state_1[10], q_state_1[13], q_state_1[12], q_state_1[15], q_state_1[14]};
        boolean $$_tmp_measureVar1;
        if (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] + q_state_0[9] * q_state_0[9] + q_state_1[9] * q_state_1[9] + q_state_0[11] * q_state_0[11] + q_state_1[11] * q_state_1[11] + q_state_0[13] * q_state_0[13] + q_state_1[13] * q_state_1[13] + q_state_0[15] * q_state_0[15] + q_state_1[15] * q_state_1[15] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[8] * q_state_0[8] + q_state_1[8] * q_state_1[8] + q_state_0[10] * q_state_0[10] + q_state_1[10] * q_state_1[10] + q_state_0[12] * q_state_0[12] + q_state_1[12] * q_state_1[12] + q_state_0[14] * q_state_0[14] + q_state_1[14] * q_state_1[14]) {
            q_state_0 = new float[]{0.0F, q_state_0[1], 0.0F, q_state_0[3], 0.0F, q_state_0[5], 0.0F, q_state_0[7], 0.0F, q_state_0[9], 0.0F, q_state_0[11], 0.0F, q_state_0[13], 0.0F, q_state_0[15]};
            q_state_1 = new float[]{0.0F, q_state_1[1], 0.0F, q_state_1[3], 0.0F, q_state_1[5], 0.0F, q_state_1[7], 0.0F, q_state_1[9], 0.0F, q_state_1[11], 0.0F, q_state_1[13], 0.0F, q_state_1[15]};
            $$_tmp_measureVar1 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], 0.0F, q_state_0[2], 0.0F, q_state_0[4], 0.0F, q_state_0[6], 0.0F, q_state_0[8], 0.0F, q_state_0[10], 0.0F, q_state_0[12], 0.0F, q_state_0[14], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F, q_state_1[2], 0.0F, q_state_1[4], 0.0F, q_state_1[6], 0.0F, q_state_1[8], 0.0F, q_state_1[10], 0.0F, q_state_1[12], 0.0F, q_state_1[14], 0.0F};
            $$_tmp_measureVar1 = false;
        }
        return $$_tmp_measureVar1;
    }
}
