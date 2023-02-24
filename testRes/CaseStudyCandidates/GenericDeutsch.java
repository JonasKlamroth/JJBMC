package CaseStudyCandidates;
public class GenericDeutsch {

    public GenericDeutsch() {
        super();
    }
    public static final int N = 2;
    /*@
      requires f != null && f.length == 1 << N;
      requires (\forall int i; 0 <= i && i < f.length; f[i]) || (\forall int j; 0 <= j && j < f.length; !f[j]) || count(f) == f.length / 2;
      ensures \result <==> (count(f) == f.length / 2);
   */
    public boolean isBalanced(/*@ non_null */
            boolean[] f) {
        float[] q_state_0 = new float[]{1.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
        q_state_0 = new float[]{0.0F, 1.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
        q_state_0 = new float[]{0.70710677F, -0.70710677F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
        {
            {
                q_state_0 = new float[]{0.49999997F, -0.49999997F, 0.0F, 0.0F, 0.49999997F, -0.49999997F, 0.0F, 0.0F};
            }
        }
        {
            {
                q_state_0 = new float[]{0.35355335F, -0.35355335F, 0.35355335F, -0.35355335F, 0.35355335F, -0.35355335F, 0.35355335F, -0.35355335F};
            }
        }
        int size = 1 << N + 1;
        /*@ non_null */
        float[][] oracle = getOracle(N, f);
        q_state_0 = new float[]{0.35355335F * oracle[0][0] + -0.35355335F * oracle[0][1] + 0.35355335F * oracle[0][2] + -0.35355335F * oracle[0][3] + 0.35355335F * oracle[0][4] + -0.35355335F * oracle[0][5] + 0.35355335F * oracle[0][6] + -0.35355335F * oracle[0][7], 0.35355335F * oracle[1][0] + -0.35355335F * oracle[1][1] + 0.35355335F * oracle[1][2] + -0.35355335F * oracle[1][3] + 0.35355335F * oracle[1][4] + -0.35355335F * oracle[1][5] + 0.35355335F * oracle[1][6] + -0.35355335F * oracle[1][7], 0.35355335F * oracle[2][0] + -0.35355335F * oracle[2][1] + 0.35355335F * oracle[2][2] + -0.35355335F * oracle[2][3] + 0.35355335F * oracle[2][4] + -0.35355335F * oracle[2][5] + 0.35355335F * oracle[2][6] + -0.35355335F * oracle[2][7], 0.35355335F * oracle[3][0] + -0.35355335F * oracle[3][1] + 0.35355335F * oracle[3][2] + -0.35355335F * oracle[3][3] + 0.35355335F * oracle[3][4] + -0.35355335F * oracle[3][5] + 0.35355335F * oracle[3][6] + -0.35355335F * oracle[3][7], 0.35355335F * oracle[4][0] + -0.35355335F * oracle[4][1] + 0.35355335F * oracle[4][2] + -0.35355335F * oracle[4][3] + 0.35355335F * oracle[4][4] + -0.35355335F * oracle[4][5] + 0.35355335F * oracle[4][6] + -0.35355335F * oracle[4][7], 0.35355335F * oracle[5][0] + -0.35355335F * oracle[5][1] + 0.35355335F * oracle[5][2] + -0.35355335F * oracle[5][3] + 0.35355335F * oracle[5][4] + -0.35355335F * oracle[5][5] + 0.35355335F * oracle[5][6] + -0.35355335F * oracle[5][7], 0.35355335F * oracle[6][0] + -0.35355335F * oracle[6][1] + 0.35355335F * oracle[6][2] + -0.35355335F * oracle[6][3] + 0.35355335F * oracle[6][4] + -0.35355335F * oracle[6][5] + 0.35355335F * oracle[6][6] + -0.35355335F * oracle[6][7], 0.35355335F * oracle[7][0] + -0.35355335F * oracle[7][1] + 0.35355335F * oracle[7][2] + -0.35355335F * oracle[7][3] + 0.35355335F * oracle[7][4] + -0.35355335F * oracle[7][5] + 0.35355335F * oracle[7][6] + -0.35355335F * oracle[7][7]};
        {
            {
                q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[4], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[5], 0.70710677F * q_state_0[2] + 0.70710677F * q_state_0[6], 0.70710677F * q_state_0[3] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[4], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[5], 0.70710677F * q_state_0[2] + -0.70710677F * q_state_0[6], 0.70710677F * q_state_0[3] + -0.70710677F * q_state_0[7]};
            }
        }
        {
            {
                q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[3], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[3], 0.70710677F * q_state_0[4] + 0.70710677F * q_state_0[6], 0.70710677F * q_state_0[5] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[4] + -0.70710677F * q_state_0[6], 0.70710677F * q_state_0[5] + -0.70710677F * q_state_0[7]};
            }
        }
        boolean res = false;
        {
            {
                boolean $$_tmp_measureVar1;
                if (q_state_0[4] * q_state_0[4] + q_state_0[5] * q_state_0[5] + q_state_0[6] * q_state_0[6] + q_state_0[7] * q_state_0[7] > q_state_0[0] * q_state_0[0] + q_state_0[1] * q_state_0[1] + q_state_0[2] * q_state_0[2] + q_state_0[3] * q_state_0[3]) {
                    q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7]};
                    $$_tmp_measureVar1 = true;
                } else {
                    q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.0F, 0.0F, 0.0F, 0.0F};
                    $$_tmp_measureVar1 = false;
                }
                res |= $$_tmp_measureVar1;
            }
        }
        {
            {
                boolean $$_tmp_measureVar2;
                if (q_state_0[2] * q_state_0[2] + q_state_0[3] * q_state_0[3] + q_state_0[6] * q_state_0[6] + q_state_0[7] * q_state_0[7] > q_state_0[0] * q_state_0[0] + q_state_0[1] * q_state_0[1] + q_state_0[4] * q_state_0[4] + q_state_0[5] * q_state_0[5]) {
                    q_state_0 = new float[]{0.0F, 0.0F, q_state_0[2], q_state_0[3], 0.0F, 0.0F, q_state_0[6], q_state_0[7]};
                    $$_tmp_measureVar2 = true;
                } else {
                    q_state_0 = new float[]{q_state_0[0], q_state_0[1], 0.0F, 0.0F, q_state_0[4], q_state_0[5], 0.0F, 0.0F};
                    $$_tmp_measureVar2 = false;
                }
                res |= $$_tmp_measureVar2;
            }
        }
        return res;
    }
    /*@
      requires f != null && f.length == 1 << 2;
      requires (\forall int i; 0 <= i && i < f.length; f[i]) || (\forall int j; 0 <= j && j < f.length; !f[j]) || count(f) == f.length / 2;
      ensures \result <==> (count(f) == f.length / 2);
   */

    public boolean isBalancedHandTranslated(/*@ non_null */
            boolean[] f) {
        float[] q_state_0 = new float[]{1.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
        q_state_0 = new float[]{0.0F, 1.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
        q_state_0 = new float[]{0.70710677F, -0.70710677F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
        q_state_0 = new float[]{0.49999997F, -0.49999997F, 0.0F, 0.0F, 0.49999997F, -0.49999997F, 0.0F, 0.0F};
        q_state_0 = new float[]{0.35355335F, -0.35355335F, 0.35355335F, -0.35355335F, 0.35355335F, -0.35355335F, 0.35355335F, -0.35355335F};
        /*@ non_null */
        float[][] oracle = getOracle(2, f);
        q_state_0 = new float[]{0.35355335F * oracle[0][0] + -0.35355335F * oracle[0][1] + 0.35355335F * oracle[0][2] + -0.35355335F * oracle[0][3] + 0.35355335F * oracle[0][4] + -0.35355335F * oracle[0][5] + 0.35355335F * oracle[0][6] + -0.35355335F * oracle[0][7], 0.35355335F * oracle[1][0] + -0.35355335F * oracle[1][1] + 0.35355335F * oracle[1][2] + -0.35355335F * oracle[1][3] + 0.35355335F * oracle[1][4] + -0.35355335F * oracle[1][5] + 0.35355335F * oracle[1][6] + -0.35355335F * oracle[1][7], 0.35355335F * oracle[2][0] + -0.35355335F * oracle[2][1] + 0.35355335F * oracle[2][2] + -0.35355335F * oracle[2][3] + 0.35355335F * oracle[2][4] + -0.35355335F * oracle[2][5] + 0.35355335F * oracle[2][6] + -0.35355335F * oracle[2][7], 0.35355335F * oracle[3][0] + -0.35355335F * oracle[3][1] + 0.35355335F * oracle[3][2] + -0.35355335F * oracle[3][3] + 0.35355335F * oracle[3][4] + -0.35355335F * oracle[3][5] + 0.35355335F * oracle[3][6] + -0.35355335F * oracle[3][7], 0.35355335F * oracle[4][0] + -0.35355335F * oracle[4][1] + 0.35355335F * oracle[4][2] + -0.35355335F * oracle[4][3] + 0.35355335F * oracle[4][4] + -0.35355335F * oracle[4][5] + 0.35355335F * oracle[4][6] + -0.35355335F * oracle[4][7], 0.35355335F * oracle[5][0] + -0.35355335F * oracle[5][1] + 0.35355335F * oracle[5][2] + -0.35355335F * oracle[5][3] + 0.35355335F * oracle[5][4] + -0.35355335F * oracle[5][5] + 0.35355335F * oracle[5][6] + -0.35355335F * oracle[5][7], 0.35355335F * oracle[6][0] + -0.35355335F * oracle[6][1] + 0.35355335F * oracle[6][2] + -0.35355335F * oracle[6][3] + 0.35355335F * oracle[6][4] + -0.35355335F * oracle[6][5] + 0.35355335F * oracle[6][6] + -0.35355335F * oracle[6][7], 0.35355335F * oracle[7][0] + -0.35355335F * oracle[7][1] + 0.35355335F * oracle[7][2] + -0.35355335F * oracle[7][3] + 0.35355335F * oracle[7][4] + -0.35355335F * oracle[7][5] + 0.35355335F * oracle[7][6] + -0.35355335F * oracle[7][7]};
        q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[4], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[5], 0.70710677F * q_state_0[2] + 0.70710677F * q_state_0[6], 0.70710677F * q_state_0[3] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[4], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[5], 0.70710677F * q_state_0[2] + -0.70710677F * q_state_0[6], 0.70710677F * q_state_0[3] + -0.70710677F * q_state_0[7]};
        q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[3], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[3], 0.70710677F * q_state_0[4] + 0.70710677F * q_state_0[6], 0.70710677F * q_state_0[5] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[4] + -0.70710677F * q_state_0[6], 0.70710677F * q_state_0[5] + -0.70710677F * q_state_0[7]};
        boolean res = false;
        boolean $$_tmp_measureVar3;
        if (q_state_0[4] * q_state_0[4] + q_state_0[5] * q_state_0[5] + q_state_0[6] * q_state_0[6] + q_state_0[7] * q_state_0[7] > q_state_0[0] * q_state_0[0] + q_state_0[1] * q_state_0[1] + q_state_0[2] * q_state_0[2] + q_state_0[3] * q_state_0[3]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7]};
            $$_tmp_measureVar3 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar3 = false;
        }
        res |= $$_tmp_measureVar3;
        boolean $$_tmp_measureVar4;
        if (q_state_0[2] * q_state_0[2] + q_state_0[3] * q_state_0[3] + q_state_0[6] * q_state_0[6] + q_state_0[7] * q_state_0[7] > q_state_0[0] * q_state_0[0] + q_state_0[1] * q_state_0[1] + q_state_0[4] * q_state_0[4] + q_state_0[5] * q_state_0[5]) {
            q_state_0 = new float[]{0.0F, 0.0F, q_state_0[2], q_state_0[3], 0.0F, 0.0F, q_state_0[6], q_state_0[7]};
            $$_tmp_measureVar4 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], 0.0F, 0.0F, q_state_0[4], q_state_0[5], 0.0F, 0.0F};
            $$_tmp_measureVar4 = false;
        }
        res |= $$_tmp_measureVar4;
        boolean $$_tmp_measureVar5;
        if (q_state_0[1] * q_state_0[1] + q_state_0[3] * q_state_0[3] + q_state_0[5] * q_state_0[5] + q_state_0[7] * q_state_0[7] > q_state_0[0] * q_state_0[0] + q_state_0[2] * q_state_0[2] + q_state_0[4] * q_state_0[4] + q_state_0[6] * q_state_0[6]) {
            q_state_0 = new float[]{0.0F, q_state_0[1], 0.0F, q_state_0[3], 0.0F, q_state_0[5], 0.0F, q_state_0[7]};
            $$_tmp_measureVar5 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], 0.0F, q_state_0[2], 0.0F, q_state_0[4], 0.0F, q_state_0[6], 0.0F};
            $$_tmp_measureVar5 = false;
        }
        res |= $$_tmp_measureVar5;
        return res;
    }

    public float[][] getOracle(int N, /*@ non_null */
                               boolean[] f) {
        int size = 1 << N + 1;
        /*@ non_null */
        float[][] oracle = new float[size][size];
        for (int i = 0; i < size; ++i) {
            for (int j = 0; j < size; ++j) {
                oracle[i][j] = 0.0F;
                float val = f[i / 2] ? 1.0F : 0.0F;
                if (i == j) {
                    oracle[i][j] = 1.0F - val;
                }
                int even = (i % 2) * 2 - 1;
                if (i == j + even) {
                    oracle[i][j] = val;
                }
            }
        }
        return oracle;
    }

    /*@ pure */
    public static int count(/*@ non_null */
            boolean[] f) {
        int i = 0;
        for (int j = 0; j < f.length; j++) {
            if (f[j]) {
                ++i;
            }
        }
        return i;
    }
}