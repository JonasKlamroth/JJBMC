public class Deutsch {
    /*@
      requires f != null && f.length == 2;
      ensures \result <==> (f[0] != f[1]);
   */

    public static boolean isBalanced(/*@ non_null */
            boolean[] f) {
        if (f == null || f.length != 2) {
            throw new IllegalArgumentException("Input for Deutschalgorithm has to be boolean array of size 2.");
        }
        /*@ non_null */
        float[][] m = new float[][]{new float[]{!f[0] ? 1.0F : 0.0F, f[0] ? 1.0F : 0.0F, 0.0F, 0.0F}, new float[]{f[0] ? 1.0F : 0.0F, !f[0] ? 1.0F : 0.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, !f[1] ? 1.0F : 0.0F, f[1] ? 1.0F : 0.0F}, new float[]{0.0F, 0.0F, f[1] ? 1.0F : 0.0F, !f[1] ? 1.0F : 0.0F}};
        float[][] q_state_0 = new float[][]{new float[]{1.0F}, new float[]{0.0F}, new float[]{0.0F}, new float[]{0.0F}};
        float[][] q_state_1 = new float[][]{new float[]{0.0F}, new float[]{0.0F}, new float[]{0.0F}, new float[]{0.0F}};
        q_state_0 = new float[][]{new float[]{0.0F}, new float[]{1.0F}, new float[]{0.0F}, new float[]{0.0F}};
        q_state_1 = new float[][]{new float[]{0.0F}, new float[]{0.0F}, new float[]{0.0F}, new float[]{0.0F}};
        q_state_0 = new float[][]{new float[]{0.70710677F}, new float[]{-0.70710677F}, new float[]{0.0F}, new float[]{0.0F}};
        q_state_1 = new float[][]{new float[]{0.0F}, new float[]{0.0F}, new float[]{0.0F}, new float[]{0.0F}};
        q_state_0 = new float[][]{new float[]{0.49999997F}, new float[]{-0.49999997F}, new float[]{0.49999997F}, new float[]{-0.49999997F}};
        q_state_1 = new float[][]{new float[]{0.0F}, new float[]{0.0F}, new float[]{0.0F}, new float[]{0.0F}};
        q_state_0 = new float[][]{new float[]{0.49999997F * m[0][0] + -0.49999997F * m[0][1] + 0.49999997F * m[0][2] + -0.49999997F * m[0][3]}, new float[]{0.49999997F * m[1][0] + -0.49999997F * m[1][1] + 0.49999997F * m[1][2] + -0.49999997F * m[1][3]}, new float[]{0.49999997F * m[2][0] + -0.49999997F * m[2][1] + 0.49999997F * m[2][2] + -0.49999997F * m[2][3]}, new float[]{0.49999997F * m[3][0] + -0.49999997F * m[3][1] + 0.49999997F * m[3][2] + -0.49999997F * m[3][3]}};
        q_state_1 = new float[][]{new float[]{0.0F}, new float[]{0.0F}, new float[]{0.0F}, new float[]{0.0F}};
        q_state_0 = new float[][]{new float[]{0.70710677F * (0.49999997F * m[0][0] + -0.49999997F * m[0][1] + 0.49999997F * m[0][2] + -0.49999997F * m[0][3]) + 0.70710677F * (0.49999997F * m[2][0] + -0.49999997F * m[2][1] + 0.49999997F * m[2][2] + -0.49999997F * m[2][3])}, new float[]{0.70710677F * (0.49999997F * m[1][0] + -0.49999997F * m[1][1] + 0.49999997F * m[1][2] + -0.49999997F * m[1][3]) + 0.70710677F * (0.49999997F * m[3][0] + -0.49999997F * m[3][1] + 0.49999997F * m[3][2] + -0.49999997F * m[3][3])}, new float[]{0.70710677F * (0.49999997F * m[0][0] + -0.49999997F * m[0][1] + 0.49999997F * m[0][2] + -0.49999997F * m[0][3]) + -0.70710677F * (0.49999997F * m[2][0] + -0.49999997F * m[2][1] + 0.49999997F * m[2][2] + -0.49999997F * m[2][3])}, new float[]{0.70710677F * (0.49999997F * m[1][0] + -0.49999997F * m[1][1] + 0.49999997F * m[1][2] + -0.49999997F * m[1][3]) + -0.70710677F * (0.49999997F * m[3][0] + -0.49999997F * m[3][1] + 0.49999997F * m[3][2] + -0.49999997F * m[3][3])}};
        q_state_1 = new float[][]{new float[]{0.0F}, new float[]{0.0F}, new float[]{0.0F}, new float[]{0.0F}};
        boolean $$_tmp_measureVar1;
        if ((q_state_0[2][0] * q_state_0[2][0] + q_state_1[2][0] * q_state_1[2][0]) * (q_state_0[2][0] * q_state_0[2][0] + q_state_1[2][0] * q_state_1[2][0]) + (q_state_0[3][0] * q_state_0[3][0] + q_state_1[3][0] * q_state_1[3][0]) * (q_state_0[3][0] * q_state_0[3][0] + q_state_1[3][0] * q_state_1[3][0]) > (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0]) * (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0]) + (q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) * (q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0])) {
            q_state_0 = new float[][]{new float[]{0.0F}, new float[]{0.0F}, new float[]{q_state_0[2][0]}, new float[]{q_state_0[3][0]}};
            q_state_1 = new float[][]{new float[]{0.0F}, new float[]{0.0F}, new float[]{q_state_1[2][0]}, new float[]{q_state_1[3][0]}};
            $$_tmp_measureVar1 = true;
        } else {
            q_state_0 = new float[][]{new float[]{q_state_0[0][0]}, new float[]{q_state_0[1][0]}, new float[]{0.0F}, new float[]{0.0F}};
            q_state_1 = new float[][]{new float[]{q_state_1[0][0]}, new float[]{q_state_1[1][0]}, new float[]{0.0F}, new float[]{0.0F}};
            $$_tmp_measureVar1 = false;
        }
        return $$_tmp_measureVar1;
    }
}