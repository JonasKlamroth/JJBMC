import org.cprover.CProver;

public class BB84 {

    public BB84() {
        super();
    }

    public boolean generateKeyBit(boolean aprime, boolean bprime) {
        float[][] q_state_0 = new float[][]{new float[]{1.0F}, new float[]{0.0F}};
        float[][] q_state_1 = new float[][]{new float[]{0.0F}, new float[]{0.0F}};
        q_state_0 = new float[][]{new float[]{0.70710677F}, new float[]{0.70710677F}};
        q_state_1 = new float[][]{new float[]{0.0F}, new float[]{0.0F}};
        boolean $$_tmp_measureVar1;
        if (CProver.nondetBoolean()) {
            q_state_0 = new float[][]{new float[]{q_state_0[0][0]}, new float[]{0.0F}};
            q_state_1 = new float[][]{new float[]{q_state_1[0][0]}, new float[]{0.0F}};
            $$_tmp_measureVar1 = false;
        } else {
            q_state_0 = new float[][]{new float[]{0.0F}, new float[]{q_state_0[1][0]}};
            q_state_1 = new float[][]{new float[]{0.0F}, new float[]{q_state_1[1][0]}};
            $$_tmp_measureVar1 = true;
        }
        boolean a = $$_tmp_measureVar1;
        if (aprime) {
            q_state_0 = new float[][]{new float[]{0.70710677F * q_state_0[0][0] + 0.70710677F * q_state_0[1][0]}, new float[]{0.70710677F * q_state_0[0][0] + -0.70710677F * q_state_0[1][0]}};
            q_state_1 = new float[][]{new float[]{0.70710677F * q_state_1[0][0] + 0.70710677F * q_state_1[1][0]}, new float[]{0.70710677F * q_state_1[0][0] + -0.70710677F * q_state_1[1][0]}};
        }
        if (bprime) {
            q_state_0 = new float[][]{new float[]{0.70710677F * q_state_0[0][0] + 0.70710677F * q_state_0[1][0]}, new float[]{0.70710677F * q_state_0[0][0] + -0.70710677F * q_state_0[1][0]}};
            q_state_1 = new float[][]{new float[]{0.70710677F * q_state_1[0][0] + 0.70710677F * q_state_1[1][0]}, new float[]{0.70710677F * q_state_1[0][0] + -0.70710677F * q_state_1[1][0]}};
        }
        boolean $$_tmp_measureVar2;
        if ((q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) * (q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) > (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0]) * (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0])) {
            q_state_0 = new float[][]{new float[]{0.0F}, new float[]{q_state_0[1][0]}};
            q_state_1 = new float[][]{new float[]{0.0F}, new float[]{q_state_1[1][0]}};
            $$_tmp_measureVar2 = true;
        } else {
            q_state_0 = new float[][]{new float[]{q_state_0[0][0]}, new float[]{0.0F}};
            q_state_1 = new float[][]{new float[]{q_state_1[0][0]}, new float[]{0.0F}};
            $$_tmp_measureVar2 = false;
        }
        boolean b = $$_tmp_measureVar2;
        assert aprime != bprime || a == b;
        return a;
    }


}
