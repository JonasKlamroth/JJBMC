

public class Grover {

  public Grover() {
    super();
  }
  /*@ non_null */
  private static final float[][] T = new float[][]{new float[]{1.0F, 0.0F}, new float[]{0.0F, 0.70710677F}};
  /*@ non_null */
  private static final float[][] Tc = new float[][]{new float[]{0.0F, 0.0F}, new float[]{0.0F, 0.70710677F}};
  /*@ non_null */
  private static final float[][] Tc_t = new float[][]{new float[]{0.0F, 0.0F}, new float[]{0.0F, -0.70710677F}};
    /*@
      ensures ((val >= 0 && val < 4) ==> \result == val) && ((val < 0 || val > 3) ==> \result == -1);
   */

  public static int grover2(int val) {
    if (val < 0 || val > 3) {
      return -1;
    }
    /*@ non_null */
    final float[][] oracle2 = new float[][]{new float[]{val == 0 ? 1.0F : -1.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, val == 1 ? 1.0F : -1.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, val == 2 ? 1.0F : -1.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, val == 3 ? 1.0F : -1.0F}};
    float[] q_state_0 = new float[]{1.0F, 0.0F, 0.0F, 0.0F};
    float[] q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{0.70710677F, 0.0F, 0.70710677F, 0.0F};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{0.49999997F, 0.49999997F, 0.49999997F, 0.49999997F};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{0.49999997F * oracle2[0][0] + 0.49999997F * oracle2[0][1] + 0.49999997F * oracle2[0][2] + 0.49999997F * oracle2[0][3], 0.49999997F * oracle2[1][0] + 0.49999997F * oracle2[1][1] + 0.49999997F * oracle2[1][2] + 0.49999997F * oracle2[1][3], 0.49999997F * oracle2[2][0] + 0.49999997F * oracle2[2][1] + 0.49999997F * oracle2[2][2] + 0.49999997F * oracle2[2][3], 0.49999997F * oracle2[3][0] + 0.49999997F * oracle2[3][1] + 0.49999997F * oracle2[3][2] + 0.49999997F * oracle2[3][3]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[3], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[3]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[1], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[1], 0.70710677F * q_state_0[2] + 0.70710677F * q_state_0[3], 0.70710677F * q_state_0[2] + -0.70710677F * q_state_0[3]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{q_state_0[0], q_state_0[1], -1.0F * q_state_0[2], -1.0F * q_state_0[3]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{q_state_0[0], -1.0F * q_state_0[1], q_state_0[2], -1.0F * q_state_0[3]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], -1.0F * q_state_0[3]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[3], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[3]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[1], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[1], 0.70710677F * q_state_0[2] + 0.70710677F * q_state_0[3], 0.70710677F * q_state_0[2] + -0.70710677F * q_state_0[3]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    boolean $$_tmp_measureVar1;
    if ((q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) * (q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) + (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) * (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) > (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) * (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) + (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) * (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1])) {
      q_state_0 = new float[]{0.0F, 0.0F, q_state_0[2], q_state_0[3]};
      q_state_1 = new float[]{0.0F, 0.0F, q_state_1[2], q_state_1[3]};
      $$_tmp_measureVar1 = true;
    } else {
      q_state_0 = new float[]{q_state_0[0], q_state_0[1], 0.0F, 0.0F};
      q_state_1 = new float[]{q_state_1[0], q_state_1[1], 0.0F, 0.0F};
      $$_tmp_measureVar1 = false;
    }
    boolean res1 = $$_tmp_measureVar1;
    boolean $$_tmp_measureVar2;
    if ((q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) * (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) + (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) * (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) > (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) * (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) + (q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) * (q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2])) {
      q_state_0 = new float[]{0.0F, q_state_0[1], 0.0F, q_state_0[3]};
      q_state_1 = new float[]{0.0F, q_state_1[1], 0.0F, q_state_1[3]};
      $$_tmp_measureVar2 = true;
    } else {
      q_state_0 = new float[]{q_state_0[0], 0.0F, q_state_0[2], 0.0F};
      q_state_1 = new float[]{q_state_1[0], 0.0F, q_state_1[2], 0.0F};
      $$_tmp_measureVar2 = false;
    }
    boolean res2 = $$_tmp_measureVar2;
    return (res1 ? 2 : 0) + (res2 ? 1 : 0);
  }
    /*@
      ensures ((val >= 0 && val < 8) ==> \result == val) && ((val < 0 || val > 7) ==> \result == -1);
   */

  public static int grover3(int val) {
    if (val < 0 || val > 7) {
      return -1;
    }
    /*@ non_null */
    final float[][] oracle4 = new float[][]{new float[]{val == 0 ? 1.0F : -1.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, val == 1 ? 1.0F : -1.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, val == 2 ? 1.0F : -1.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, val == 3 ? 1.0F : -1.0F, 0.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, 0.0F, val == 4 ? 1.0F : -1.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, val == 5 ? 1.0F : -1.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, val == 6 ? 1.0F : -1.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, val == 7 ? 1.0F : -1.0F}};
    float[] q_state_0 = new float[]{1.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
    float[] q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{0.70710677F, 0.0F, 0.0F, 0.0F, 0.70710677F, 0.0F, 0.0F, 0.0F};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{0.49999997F, 0.0F, 0.49999997F, 0.0F, 0.49999997F, 0.0F, 0.49999997F, 0.0F};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{0.35355335F, 0.35355335F, 0.35355335F, 0.35355335F, 0.35355335F, 0.35355335F, 0.35355335F, 0.35355335F};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{0.35355335F * oracle4[0][0] + 0.35355335F * oracle4[0][1] + 0.35355335F * oracle4[0][2] + 0.35355335F * oracle4[0][3] + 0.35355335F * oracle4[0][4] + 0.35355335F * oracle4[0][5] + 0.35355335F * oracle4[0][6] + 0.35355335F * oracle4[0][7], 0.35355335F * oracle4[1][0] + 0.35355335F * oracle4[1][1] + 0.35355335F * oracle4[1][2] + 0.35355335F * oracle4[1][3] + 0.35355335F * oracle4[1][4] + 0.35355335F * oracle4[1][5] + 0.35355335F * oracle4[1][6] + 0.35355335F * oracle4[1][7], 0.35355335F * oracle4[2][0] + 0.35355335F * oracle4[2][1] + 0.35355335F * oracle4[2][2] + 0.35355335F * oracle4[2][3] + 0.35355335F * oracle4[2][4] + 0.35355335F * oracle4[2][5] + 0.35355335F * oracle4[2][6] + 0.35355335F * oracle4[2][7], 0.35355335F * oracle4[3][0] + 0.35355335F * oracle4[3][1] + 0.35355335F * oracle4[3][2] + 0.35355335F * oracle4[3][3] + 0.35355335F * oracle4[3][4] + 0.35355335F * oracle4[3][5] + 0.35355335F * oracle4[3][6] + 0.35355335F * oracle4[3][7], 0.35355335F * oracle4[4][0] + 0.35355335F * oracle4[4][1] + 0.35355335F * oracle4[4][2] + 0.35355335F * oracle4[4][3] + 0.35355335F * oracle4[4][4] + 0.35355335F * oracle4[4][5] + 0.35355335F * oracle4[4][6] + 0.35355335F * oracle4[4][7], 0.35355335F * oracle4[5][0] + 0.35355335F * oracle4[5][1] + 0.35355335F * oracle4[5][2] + 0.35355335F * oracle4[5][3] + 0.35355335F * oracle4[5][4] + 0.35355335F * oracle4[5][5] + 0.35355335F * oracle4[5][6] + 0.35355335F * oracle4[5][7], 0.35355335F * oracle4[6][0] + 0.35355335F * oracle4[6][1] + 0.35355335F * oracle4[6][2] + 0.35355335F * oracle4[6][3] + 0.35355335F * oracle4[6][4] + 0.35355335F * oracle4[6][5] + 0.35355335F * oracle4[6][6] + 0.35355335F * oracle4[6][7], 0.35355335F * oracle4[7][0] + 0.35355335F * oracle4[7][1] + 0.35355335F * oracle4[7][2] + 0.35355335F * oracle4[7][3] + 0.35355335F * oracle4[7][4] + 0.35355335F * oracle4[7][5] + 0.35355335F * oracle4[7][6] + 0.35355335F * oracle4[7][7]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[4], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[5], 0.70710677F * q_state_0[2] + 0.70710677F * q_state_0[6], 0.70710677F * q_state_0[3] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[4], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[5], 0.70710677F * q_state_0[2] + -0.70710677F * q_state_0[6], 0.70710677F * q_state_0[3] + -0.70710677F * q_state_0[7]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[3], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[3], 0.70710677F * q_state_0[4] + 0.70710677F * q_state_0[6], 0.70710677F * q_state_0[5] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[4] + -0.70710677F * q_state_0[6], 0.70710677F * q_state_0[5] + -0.70710677F * q_state_0[7]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[1], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[1], 0.70710677F * q_state_0[2] + 0.70710677F * q_state_0[3], 0.70710677F * q_state_0[2] + -0.70710677F * q_state_0[3], 0.70710677F * q_state_0[4] + 0.70710677F * q_state_0[5], 0.70710677F * q_state_0[4] + -0.70710677F * q_state_0[5], 0.70710677F * q_state_0[6] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[6] + -0.70710677F * q_state_0[7]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{q_state_0[2], q_state_0[3], q_state_0[0], q_state_0[1], q_state_0[6], q_state_0[7], q_state_0[4], q_state_0[5]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{q_state_0[1], q_state_0[0], q_state_0[3], q_state_0[2], q_state_0[5], q_state_0[4], q_state_0[7], q_state_0[6]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[3], q_state_0[2], q_state_0[4], q_state_0[5], q_state_0[7], q_state_0[6]};
    q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
    q_state_0 = new float[]{q_state_0[0], 0.70710677F * q_state_0[1], q_state_0[2], 0.70710677F * q_state_0[3], q_state_0[4], 0.70710677F * q_state_0[5], q_state_0[6], 0.70710677F * q_state_0[7]};
    q_state_1 = new float[]{0.0F, Tc_t[1][1] * q_state_0[1], 0.0F, Tc_t[1][1] * q_state_0[3], 0.0F, Tc_t[1][1] * q_state_0[5], 0.0F, Tc_t[1][1] * q_state_0[7]};
    q_state_0 = new float[]{q_state_0[0], q_state_0[2], q_state_0[1], q_state_0[3], q_state_0[4], q_state_0[6], q_state_0[5], q_state_0[7]};
    q_state_1 = new float[]{0.0F, 0.0F, q_state_1[1], q_state_1[3], 0.0F, 0.0F, q_state_1[5], q_state_1[7]};
    q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[3], q_state_0[2], q_state_0[4], q_state_0[5], q_state_0[7], q_state_0[6]};
    q_state_1 = new float[]{0.0F, 0.0F, q_state_1[3], q_state_1[2], 0.0F, 0.0F, q_state_1[7], q_state_1[6]};
    q_state_0 = new float[]{q_state_0[0], q_state_0[2], q_state_0[1], q_state_0[3], q_state_0[4], q_state_0[6], q_state_0[5], q_state_0[7]};
    q_state_1 = new float[]{0.0F, q_state_1[2], 0.0F, q_state_1[3], 0.0F, q_state_1[6], 0.0F, q_state_1[7]};
    q_state_0 = new float[]{q_state_0[0], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_1[1], q_state_0[2], 0.70710677F * q_state_0[3] + -0.70710677F * q_state_1[3], q_state_0[4], 0.70710677F * q_state_0[5] + -0.70710677F * q_state_1[5], q_state_0[6], 0.70710677F * q_state_0[7] + -0.70710677F * q_state_1[7]};
    q_state_1 = new float[]{0.0F, 0.70710677F * q_state_1[1] + 0.70710677F * q_state_0[1], 0.0F, 0.70710677F * q_state_1[3] + 0.70710677F * q_state_0[3], 0.0F, 0.70710677F * q_state_1[5] + 0.70710677F * q_state_0[5], 0.0F, 0.70710677F * q_state_1[7] + 0.70710677F * q_state_0[7]};
    q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[3], q_state_0[2], q_state_0[4], q_state_0[5], q_state_0[7], q_state_0[6]};
    q_state_1 = new float[]{0.0F, q_state_1[1], q_state_1[3], 0.0F, 0.0F, q_state_1[5], q_state_1[7], 0.0F};
    q_state_0 = new float[]{q_state_0[0], 0.70710677F * q_state_0[1] + -1.0F * (Tc_t[1][1] * q_state_1[1]), q_state_0[2], 0.70710677F * q_state_0[3], q_state_0[4], 0.70710677F * q_state_0[5] + -1.0F * (Tc_t[1][1] * q_state_1[5]), q_state_0[6], 0.70710677F * q_state_0[7]};
    q_state_1 = new float[]{0.0F, 0.70710677F * q_state_1[1] + Tc_t[1][1] * q_state_0[1], q_state_1[2], Tc_t[1][1] * q_state_0[3], 0.0F, 0.70710677F * q_state_1[5] + Tc_t[1][1] * q_state_0[5], q_state_1[6], Tc_t[1][1] * q_state_0[7]};
    q_state_0 = new float[]{q_state_0[0], q_state_0[2], q_state_0[1], q_state_0[3], q_state_0[4], q_state_0[6], q_state_0[5], q_state_0[7]};
    q_state_1 = new float[]{0.0F, q_state_1[2], q_state_1[1], q_state_1[3], 0.0F, q_state_1[6], q_state_1[5], q_state_1[7]};
    q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[3], q_state_0[2], q_state_0[4], q_state_0[5], q_state_0[7], q_state_0[6]};
    q_state_1 = new float[]{0.0F, q_state_1[1], q_state_1[3], q_state_1[2], 0.0F, q_state_1[5], q_state_1[7], q_state_1[6]};
    q_state_0 = new float[]{q_state_0[0], q_state_0[2], q_state_0[1], q_state_0[3], q_state_0[4], q_state_0[6], q_state_0[5], q_state_0[7]};
    q_state_1 = new float[]{0.0F, q_state_1[2], q_state_1[1], q_state_1[3], 0.0F, q_state_1[6], q_state_1[5], q_state_1[7]};
    q_state_0 = new float[]{q_state_0[0], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_1[1], q_state_0[2], 0.70710677F * q_state_0[3] + -0.70710677F * q_state_1[3], q_state_0[4], 0.70710677F * q_state_0[5] + -0.70710677F * q_state_1[5], q_state_0[6], 0.70710677F * q_state_0[7] + -0.70710677F * q_state_1[7]};
    q_state_1 = new float[]{0.0F, 0.70710677F * q_state_1[1] + 0.70710677F * q_state_0[1], q_state_1[2], 0.70710677F * q_state_1[3] + 0.70710677F * q_state_0[3], 0.0F, 0.70710677F * q_state_1[5] + 0.70710677F * q_state_0[5], q_state_1[6], 0.70710677F * q_state_1[7] + 0.70710677F * q_state_0[7]};
    q_state_0 = new float[]{q_state_0[0], q_state_0[1], 0.70710677F * q_state_0[2] + -0.70710677F * q_state_1[2], 0.70710677F * q_state_0[3] + -0.70710677F * q_state_1[3], q_state_0[4], q_state_0[5], 0.70710677F * q_state_0[6] + -0.70710677F * q_state_1[6], 0.70710677F * q_state_0[7] + -0.70710677F * q_state_1[7]};
    q_state_1 = new float[]{0.0F, q_state_1[1], 0.70710677F * q_state_1[2] + 0.70710677F * q_state_0[2], 0.70710677F * q_state_1[3] + 0.70710677F * q_state_0[3], 0.0F, q_state_1[5], 0.70710677F * q_state_1[6] + 0.70710677F * q_state_0[6], 0.70710677F * q_state_1[7] + 0.70710677F * q_state_0[7]};
    q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[6], q_state_0[7], q_state_0[4], q_state_0[5]};
    q_state_1 = new float[]{0.0F, q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[6], q_state_1[7], 0.0F, q_state_1[5]};
    q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.70710677F * q_state_0[4] + -0.70710677F * q_state_1[4], 0.70710677F * q_state_0[5] + -0.70710677F * q_state_1[5], 0.70710677F * q_state_0[6], 0.70710677F * q_state_0[7] + -0.70710677F * q_state_1[7]};
    q_state_1 = new float[]{0.0F, q_state_1[1], q_state_1[2], q_state_1[3], 0.70710677F * q_state_1[4] + 0.70710677F * q_state_0[4], 0.70710677F * q_state_1[5] + 0.70710677F * q_state_0[5], 0.70710677F * q_state_0[6], 0.70710677F * q_state_1[7] + 0.70710677F * q_state_0[7]};
    q_state_0 = new float[]{q_state_0[0], q_state_0[1], 0.70710677F * q_state_0[2] + -1.0F * (Tc_t[1][1] * q_state_1[2]), 0.70710677F * q_state_0[3] + -1.0F * (Tc_t[1][1] * q_state_1[3]), q_state_0[4], q_state_0[5], 0.70710677F * q_state_0[6] + -1.0F * (Tc_t[1][1] * q_state_1[6]), 0.70710677F * q_state_0[7] + -1.0F * (Tc_t[1][1] * q_state_1[7])};
    q_state_1 = new float[]{0.0F, q_state_1[1], 0.70710677F * q_state_1[2] + Tc_t[1][1] * q_state_0[2], 0.70710677F * q_state_1[3] + Tc_t[1][1] * q_state_0[3], q_state_1[4], q_state_1[5], 0.70710677F * q_state_1[6] + Tc_t[1][1] * q_state_0[6], 0.70710677F * q_state_1[7] + Tc_t[1][1] * q_state_0[7]};
    q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[6], q_state_0[7], q_state_0[4], q_state_0[5]};
    q_state_1 = new float[]{0.0F, q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[6], q_state_1[7], q_state_1[4], q_state_1[5]};
    q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
    q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], 0.0F, q_state_1[1], q_state_1[2], q_state_1[3]};
    q_state_0 = new float[]{q_state_0[2], q_state_0[3], q_state_0[0], q_state_0[1], q_state_0[6], q_state_0[7], q_state_0[4], q_state_0[5]};
    q_state_1 = new float[]{q_state_1[2], q_state_1[3], q_state_1[0], q_state_1[1], q_state_1[6], q_state_1[7], 0.0F, q_state_1[5]};
    q_state_0 = new float[]{q_state_0[1], q_state_0[0], q_state_0[3], q_state_0[2], q_state_0[5], q_state_0[4], q_state_0[7], q_state_0[6]};
    q_state_1 = new float[]{q_state_1[1], q_state_1[0], q_state_1[3], q_state_1[2], q_state_1[5], q_state_1[4], q_state_1[7], 0.0F};
    q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[4], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[5], 0.70710677F * q_state_0[2] + 0.70710677F * q_state_0[6], 0.70710677F * q_state_0[3] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[4], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[5], 0.70710677F * q_state_0[2] + -0.70710677F * q_state_0[6], 0.70710677F * q_state_0[3] + -0.70710677F * q_state_0[7]};
    q_state_1 = new float[]{0.70710677F * q_state_1[0] + 0.70710677F * q_state_1[4], 0.70710677F * q_state_1[1] + 0.70710677F * q_state_1[5], 0.70710677F * q_state_1[2] + 0.70710677F * q_state_1[6], 0.70710677F * q_state_1[3], 0.70710677F * q_state_1[0] + -0.70710677F * q_state_1[4], 0.70710677F * q_state_1[1] + -0.70710677F * q_state_1[5], 0.70710677F * q_state_1[2] + -0.70710677F * q_state_1[6], 0.70710677F * q_state_1[3]};
    q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + 0.70710677F * q_state_0[3], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[2], 0.70710677F * q_state_0[1] + -0.70710677F * q_state_0[3], 0.70710677F * q_state_0[4] + 0.70710677F * q_state_0[6], 0.70710677F * q_state_0[5] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[4] + -0.70710677F * q_state_0[6], 0.70710677F * q_state_0[5] + -0.70710677F * q_state_0[7]};
    q_state_1 = new float[]{0.70710677F * q_state_1[0] + 0.70710677F * q_state_1[2], 0.70710677F * q_state_1[1] + 0.70710677F * q_state_1[3], 0.70710677F * q_state_1[0] + -0.70710677F * q_state_1[2], 0.70710677F * q_state_1[1] + -0.70710677F * q_state_1[3], 0.70710677F * q_state_1[4] + 0.70710677F * q_state_1[6], 0.70710677F * q_state_1[5] + 0.70710677F * q_state_1[7], 0.70710677F * q_state_1[4] + -0.70710677F * q_state_1[6], 0.70710677F * q_state_1[5] + -0.70710677F * q_state_1[7]};
    q_state_0 = new float[]{0.70710677F * q_state_0[0] + 0.70710677F * q_state_0[1], 0.70710677F * q_state_0[0] + -0.70710677F * q_state_0[1], 0.70710677F * q_state_0[2] + 0.70710677F * q_state_0[3], 0.70710677F * q_state_0[2] + -0.70710677F * q_state_0[3], 0.70710677F * q_state_0[4] + 0.70710677F * q_state_0[5], 0.70710677F * q_state_0[4] + -0.70710677F * q_state_0[5], 0.70710677F * q_state_0[6] + 0.70710677F * q_state_0[7], 0.70710677F * q_state_0[6] + -0.70710677F * q_state_0[7]};
    q_state_1 = new float[]{0.70710677F * q_state_1[0] + 0.70710677F * q_state_1[1], 0.70710677F * q_state_1[0] + -0.70710677F * q_state_1[1], 0.70710677F * q_state_1[2] + 0.70710677F * q_state_1[3], 0.70710677F * q_state_1[2] + -0.70710677F * q_state_1[3], 0.70710677F * q_state_1[4] + 0.70710677F * q_state_1[5], 0.70710677F * q_state_1[4] + -0.70710677F * q_state_1[5], 0.70710677F * q_state_1[6] + 0.70710677F * q_state_1[7], 0.70710677F * q_state_1[6] + -0.70710677F * q_state_1[7]};
    boolean $$_tmp_measureVar3;
    if ((q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4]) * (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4]) + (q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5]) * (q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5]) + (q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6]) * (q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6]) + (q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7]) * (q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7]) > (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) * (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) + (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) * (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) + (q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) * (q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) + (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) * (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3])) {
      q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7]};
      q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7]};
      $$_tmp_measureVar3 = true;
    } else {
      q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.0F, 0.0F, 0.0F, 0.0F};
      q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], 0.0F, 0.0F, 0.0F, 0.0F};
      $$_tmp_measureVar3 = false;
    }
    boolean res1 = $$_tmp_measureVar3;
    boolean $$_tmp_measureVar4;
    if ((q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) * (q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) + (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) * (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) + (q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6]) * (q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6]) + (q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7]) * (q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7]) > (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) * (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) + (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) * (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) + (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4]) * (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4]) + (q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5]) * (q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5])) {
      q_state_0 = new float[]{0.0F, 0.0F, q_state_0[2], q_state_0[3], 0.0F, 0.0F, q_state_0[6], q_state_0[7]};
      q_state_1 = new float[]{0.0F, 0.0F, q_state_1[2], q_state_1[3], 0.0F, 0.0F, q_state_1[6], q_state_1[7]};
      $$_tmp_measureVar4 = true;
    } else {
      q_state_0 = new float[]{q_state_0[0], q_state_0[1], 0.0F, 0.0F, q_state_0[4], q_state_0[5], 0.0F, 0.0F};
      q_state_1 = new float[]{q_state_1[0], q_state_1[1], 0.0F, 0.0F, q_state_1[4], q_state_1[5], 0.0F, 0.0F};
      $$_tmp_measureVar4 = false;
    }
    boolean res2 = $$_tmp_measureVar4;
    boolean $$_tmp_measureVar5;
    if ((q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) * (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1]) + (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) * (q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) + (q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5]) * (q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5]) + (q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7]) * (q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7]) > (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) * (q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) + (q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) * (q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2]) + (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4]) * (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4]) + (q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6]) * (q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6])) {
      q_state_0 = new float[]{0.0F, q_state_0[1], 0.0F, q_state_0[3], 0.0F, q_state_0[5], 0.0F, q_state_0[7]};
      q_state_1 = new float[]{0.0F, q_state_1[1], 0.0F, q_state_1[3], 0.0F, q_state_1[5], 0.0F, q_state_1[7]};
      $$_tmp_measureVar5 = true;
    } else {
      q_state_0 = new float[]{q_state_0[0], 0.0F, q_state_0[2], 0.0F, q_state_0[4], 0.0F, q_state_0[6], 0.0F};
      q_state_1 = new float[]{q_state_1[0], 0.0F, q_state_1[2], 0.0F, q_state_1[4], 0.0F, q_state_1[6], 0.0F};
      $$_tmp_measureVar5 = false;
    }
    boolean res3 = $$_tmp_measureVar5;
    return (res1 ? 4 : 0) + (res2 ? 2 : 0) + (res3 ? 1 : 0);
  }
}
