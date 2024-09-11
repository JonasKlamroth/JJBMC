import java.util.Arrays;
public class DeutschJozsaQiskit {

    public DeutschJozsaQiskit() {
        super();
    }
    public static final int n = 2;
    /*@
      requires 0 <= oracleType <= 1;
      requires 0 <= oracleValue <= 1;
      requires 1 <= a < (1 << n);
      ensures \result == (oracleType == 1);
      assignable \nothing;
   */

    public static boolean dj(int oracleType, int oracleValue, int a, boolean $$_tmp_measureParam_0, boolean $$_tmp_measureParam_1) {
        float[] q0 = new float[]{1.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
        q0 = new float[]{0.35355335F, -0.35355335F, 0.35355335F, -0.35355335F, 0.35355335F, -0.35355335F, 0.35355335F, -0.35355335F};
        if (oracleType == 0) {
            {
                if (oracleValue == 1) {
                    {
                    }
                    q0 = new float[]{-0.35355335F, 0.35355335F, -0.35355335F, 0.35355335F, -0.35355335F, 0.35355335F, -0.35355335F, 0.35355335F};
                } else {
                    {
                    }
                }
            }
        } else {
            {
                {
                    {
                        if ((a & (1 << 0)) != 0) {
                            {
                            }
                            q0 = new float[]{q0[0], q0[1], q0[2], q0[3], q0[5], q0[4], q0[7], q0[6]};
                        }
                    }
                }
                {
                    {
                        if ((a & (1 << 1)) != 0) {
                            {
                            }
                            q0 = new float[]{q0[0], q0[1], q0[3], q0[2], q0[4], q0[5], q0[7], q0[6]};
                        }
                    }
                }
            }
        }
        q0 = new float[]{0.49999997F * q0[0] + 0.49999997F * q0[2] + 0.49999997F * q0[4] + 0.49999997F * q0[6], 0.49999997F * q0[1] + 0.49999997F * q0[3] + 0.49999997F * q0[5] + 0.49999997F * q0[7], 0.49999997F * q0[0] + -0.49999997F * q0[2] + 0.49999997F * q0[4] + -0.49999997F * q0[6], 0.49999997F * q0[1] + -0.49999997F * q0[3] + 0.49999997F * q0[5] + -0.49999997F * q0[7], 0.49999997F * q0[0] + 0.49999997F * q0[2] + -0.49999997F * q0[4] + -0.49999997F * q0[6], 0.49999997F * q0[1] + 0.49999997F * q0[3] + -0.49999997F * q0[5] + -0.49999997F * q0[7], 0.49999997F * q0[0] + -0.49999997F * q0[2] + -0.49999997F * q0[4] + 0.49999997F * q0[6], 0.49999997F * q0[1] + -0.49999997F * q0[3] + -0.49999997F * q0[5] + 0.49999997F * q0[7]};
        System.out.println(Arrays.toString(q0));
        boolean res = false;
        {
            {
                boolean $$_tmp_measureVar1;
                if ($$_tmp_measureParam_0) {
                    if (true && q0[0] == 0.0F && q0[1] == 0.0F && q0[2] == 0.0F && q0[3] == 0.0F) {
                        //@ assume false;
                    }
                    System.out.println(Arrays.toString(q0));
                    q0 = new float[]{q0[0], q0[1], q0[2], q0[3], 0.0F, 0.0F, 0.0F, 0.0F};
                    $$_tmp_measureVar1 = false;
                } else {
                    if (true && q0[4] == 0.0F && q0[5] == 0.0F && q0[6] == 0.0F && q0[7] == 0.0F) {
                        //@ assume false;
                    }
                    q0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q0[4], q0[5], q0[6], q0[7]};
                    $$_tmp_measureVar1 = true;
                }
                res |= $$_tmp_measureVar1;
            }
        }
        {
            {
                boolean $$_tmp_measureVar2;
                if ($$_tmp_measureParam_1) {
                    if (true && q0[0] == 0.0F && q0[1] == 0.0F && q0[4] == 0.0F && q0[5] == 0.0F) {
                        //@ assume false;
                    }
                    System.out.println(Arrays.toString(q0));
                    q0 = new float[]{q0[0], q0[1], 0.0F, 0.0F, q0[4], q0[5], 0.0F, 0.0F};
                    $$_tmp_measureVar2 = false;
                } else {
                    if (true && q0[2] == 0.0F && q0[3] == 0.0F && q0[6] == 0.0F && q0[7] == 0.0F) {
                        //@ assume false;
                    }
                    q0 = new float[]{0.0F, 0.0F, q0[2], q0[3], 0.0F, 0.0F, q0[6], q0[7]};
                    $$_tmp_measureVar2 = true;
                }
                res |= $$_tmp_measureVar2;
            }
        }
        return res;
    }

    public static void main(String[] args) {
        System.out.println(dj(1, 0, 4, true, true));
    }
}
