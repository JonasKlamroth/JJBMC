public class SuperdenseCoding {

    public SuperdenseCoding() {
        super();
    }

    public static void sdc(boolean b1, boolean b2) {
        float[] q_state_0 = new float[]{1.0F, 0.0F, 0.0F, 0.0F};
        float[] q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
        q_state_0 = new float[]{0.70710677F, 0.0F, 0.70710677F, 0.0F};
        q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
        q_state_0 = new float[]{0.70710677F, 0.0F, 0.0F, 0.70710677F};
        q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
        if (b2) {
            q_state_0 = new float[]{0.0F, 0.70710677F, 0.70710677F, 0.0F};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
        }
        if (b1) {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], -1.0F * q_state_0[2], -1.0F * q_state_0[3]};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], -1.0F * q_state_1[2], -1.0F * q_state_1[3]};
        }
        q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[3], q_state_0[2]};
        q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[3], q_state_1[2]};
        q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[3], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[3]};
        q_state_1 = new float[]{0.70710677F * q_state_1[0] + 0.70710677F * q_state_1[2], 0.70710677F * q_state_1[1] + 0.70710677F * q_state_1[3], 0.70710677F * q_state_1[0] + -0.70710677F * q_state_1[2], 0.70710677F * q_state_1[1] + -0.70710677F * q_state_1[3]};
        boolean $$_tmp_measureVar1;
        if (q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) {
            q_state_0 = new float[]{0.0F, 0.0F, q_state_0[2], q_state_0[3]};
            q_state_1 = new float[]{0.0F, 0.0F, q_state_1[2], q_state_1[3]};
            $$_tmp_measureVar1 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], 0.0F, 0.0F};
            $$_tmp_measureVar1 = false;
        }
        assert $$_tmp_measureVar1 == b1;
        boolean $$_tmp_measureVar2;
        if (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) {
            q_state_0 = new float[]{0.0F, q_state_0[1], 0.0F, q_state_0[3]};
            q_state_1 = new float[]{0.0F, q_state_1[1], 0.0F, q_state_1[3]};
            $$_tmp_measureVar2 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], 0.0F, q_state_0[2], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F, q_state_1[2], 0.0F};
            $$_tmp_measureVar2 = false;
        }
        assert $$_tmp_measureVar2 == b2;
    }
}
