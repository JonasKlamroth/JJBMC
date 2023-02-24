import org.cprover.CProver;

public class BB84 {

    public BB84() {
        super();
    }

    public boolean generateKeyBit(boolean aprime, boolean bprime) {
        float[] q_state_0 = new float[]{1.0F, 0.0F};
        float[] q_state_1 = new float[]{0.0F, 0.0F};
        q_state_0 = new float[]{0.70710677F, 0.70710677F};
        q_state_1 = new float[]{0.0F, 0.0F};
        boolean $$_tmp_measureVar1;
        if (CProver.nondetBoolean()) {
            if (true && q_state_0[0] == 0.0F && q_state_1[0] == 0.0F) CProver.assume(false);
            q_state_0 = new float[]{q_state_0[0], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F};
            $$_tmp_measureVar1 = false;
        } else {
            if (true && q_state_0[1] == 0.0F && q_state_1[1] == 0.0F) CProver.assume(false);
            q_state_0 = new float[]{0.0F, q_state_0[1]};
            q_state_1 = new float[]{0.0F, q_state_1[1]};
            $$_tmp_measureVar1 = true;
        }
        boolean a = $$_tmp_measureVar1;
        if (aprime) {
            q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[1], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[1]};
            q_state_1 = new float[]{0.70710677F * q_state_1[0] + 0.70710677F * q_state_1[1], 0.70710677F * q_state_1[0] + -0.70710677F * q_state_1[1]};
        }
        if (bprime) {
            q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[1], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[1]};
            q_state_1 = new float[]{0.70710677F * q_state_1[0] + 0.70710677F * q_state_1[1], 0.70710677F * q_state_1[0] + -0.70710677F * q_state_1[1]};
        }
        boolean $$_tmp_measureVar2;
        if (CProver.nondetBoolean()) {
            if (true && q_state_0[0] == 0.0F && q_state_1[0] == 0.0F) CProver.assume(false);
            q_state_0 = new float[]{q_state_0[0], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F};
            $$_tmp_measureVar2 = false;
        } else {
            if (true && q_state_0[1] == 0.0F && q_state_1[1] == 0.0F) CProver.assume(false);
            q_state_0 = new float[]{0.0F, q_state_0[1]};
            q_state_1 = new float[]{0.0F, q_state_1[1]};
            $$_tmp_measureVar2 = true;
        }
        boolean b = $$_tmp_measureVar2;
        assert aprime != bprime || a == b;
        return a;
    }
}
