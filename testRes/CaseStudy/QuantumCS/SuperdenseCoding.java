

public class SuperdenseCoding {

  public SuperdenseCoding() {
    super();
  }

  public static void sdc(boolean b1, boolean b2) {
    float[] q0 = new float[]{1.0F, 0.0F, 0.0F, 0.0F};
    float[] q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    float $$_measureVar1;
    float $$_measureVar2;
    q0 = new float[]{0.70710677F, 0.0F, 0.0F, 0.70710677F};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    if (b2) {
      {
      }
      q0 = new float[]{0.0F, 0.70710677F, 0.70710677F, 0.0F};
      q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    }
    if (b1) {
      {
      }
      q0 = new float[]{q0[0], q0[1], -1.0F * q0[2], -1.0F * q0[3]};
      q1 = new float[]{q1[0], q1[1], -1.0F * q1[2], -1.0F * q1[3]};
    }
    q0 = new float[]{0.70710677F * q0[0] + 0.70710677F * q0[3], 0.70710677F * q0[1] + 0.70710677F * q0[2], 0.70710677F * q0[0] + -0.70710677F * q0[3], 0.70710677F * q0[1] + -0.70710677F * q0[2]};
    q1 = new float[]{0.70710677F * q1[0] + 0.70710677F * q1[3], 0.70710677F * q1[1] + 0.70710677F * q1[2], 0.70710677F * q1[0] + -0.70710677F * q1[3], 0.70710677F * q1[1] + -0.70710677F * q1[2]};
    boolean $$_tmp_measureVar1;
    $$_measureVar1 = q0[0] * q0[0] + q1[0] * q1[0] + q0[1] * q0[1] + q1[1] * q1[1];
    $$_measureVar2 = q0[2] * q0[2] + q1[2] * q1[2] + q0[3] * q0[3] + q1[3] * q1[3];
    if ($$_measureVar2 > $$_measureVar1) {
      q0 = new float[]{0.0F, 0.0F, q0[2], q0[3]};
      q1 = new float[]{0.0F, 0.0F, q1[2], q1[3]};
      $$_tmp_measureVar1 = true;
      $$_measureVar1 = q0[2] * q0[2] + q1[2] * q1[2] + q0[3] * q0[3] + q1[3] * q1[3];
    } else {
      q0 = new float[]{q0[0], q0[1], 0.0F, 0.0F};
      q1 = new float[]{q1[0], q1[1], 0.0F, 0.0F};
      $$_tmp_measureVar1 = false;
      $$_measureVar1 = q0[0] * q0[0] + q1[0] * q1[0] + q0[1] * q0[1] + q1[1] * q1[1];
    }
    assert $$_measureVar1 > 0.5000017F;
    assert $$_tmp_measureVar1 == b1;
    boolean $$_tmp_measureVar2;
    $$_measureVar1 = q0[0] * q0[0] + q1[0] * q1[0] + q0[2] * q0[2] + q1[2] * q1[2];
    $$_measureVar2 = q0[1] * q0[1] + q1[1] * q1[1] + q0[3] * q0[3] + q1[3] * q1[3];
    if ($$_measureVar2 > $$_measureVar1) {
      q0 = new float[]{0.0F, q0[1], 0.0F, q0[3]};
      q1 = new float[]{0.0F, q1[1], 0.0F, q1[3]};
      $$_tmp_measureVar2 = true;
      $$_measureVar1 = q0[1] * q0[1] + q1[1] * q1[1] + q0[3] * q0[3] + q1[3] * q1[3];
    } else {
      q0 = new float[]{q0[0], 0.0F, q0[2], 0.0F};
      q1 = new float[]{q1[0], 0.0F, q1[2], 0.0F};
      $$_tmp_measureVar2 = false;
      $$_measureVar1 = q0[0] * q0[0] + q1[0] * q1[0] + q0[2] * q0[2] + q1[2] * q1[2];
    }
    assert $$_measureVar1 > 0.2500017F;
    assert $$_tmp_measureVar2 == b2;
  }
}
