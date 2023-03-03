

public class Grover {

  public Grover() {
    super();
  }
    /*@
      requires database != null && database.length == 4;
      requires (\forall int i; 0 <= i < 4; database[i] >= 0 && database[i] < 4);
      requires (\forall int i; 0 <= i < 4; (\forall int j; 0 <= j < 4; i == j || database[i] != database[j]));
      ensures ((val >= 0 && val < 4) ==> val == database[\result]);
      ensures ((val < 0 || val > 3) ==> \result == -1);
   */

  public static int grover2(/*@ non_null */
      int[] database, int val) {
    if (val < 0 || val > 3) {
      return -1;
    }
    /*@ non_null */
    final float[][] oracle2 = new float[][]{new float[]{val == database[0] ? 1.0F : -1.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, val == database[1] ? 1.0F : -1.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, val == database[2] ? 1.0F : -1.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, val == database[3] ? 1.0F : -1.0F}};
    float[] q0 = new float[]{1.0F, 0.0F, 0.0F, 0.0F};
    float[] q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{0.70710677F, 0.0F, 0.70710677F, 0.0F};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{0.49999997F, 0.49999997F, 0.49999997F, 0.49999997F};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{0.49999997F * oracle2[0][0] + 0.49999997F * oracle2[0][1] + 0.49999997F * oracle2[0][2] + 0.49999997F * oracle2[0][3], 0.49999997F * oracle2[1][0] + 0.49999997F * oracle2[1][1] + 0.49999997F * oracle2[1][2] + 0.49999997F * oracle2[1][3], 0.49999997F * oracle2[2][0] + 0.49999997F * oracle2[2][1] + 0.49999997F * oracle2[2][2] + 0.49999997F * oracle2[2][3], 0.49999997F * oracle2[3][0] + 0.49999997F * oracle2[3][1] + 0.49999997F * oracle2[3][2] + 0.49999997F * oracle2[3][3]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{0.70710677F * q0[0] + 0.70710677F * q0[2], 0.70710677F * q0[1] + 0.70710677F * q0[3], 0.70710677F * q0[0] + -0.70710677F * q0[2], 0.70710677F * q0[1] + -0.70710677F * q0[3]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{0.70710677F * q0[0] + 0.70710677F * q0[1], 0.70710677F * q0[0] + -0.70710677F * q0[1], 0.70710677F * q0[2] + 0.70710677F * q0[3], 0.70710677F * q0[2] + -0.70710677F * q0[3]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{q0[0], q0[1], -1.0F * q0[2], -1.0F * q0[3]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{q0[0], -1.0F * q0[1], q0[2], -1.0F * q0[3]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{q0[0], q0[1], q0[2], -1.0F * q0[3]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{0.70710677F * q0[0] + 0.70710677F * q0[2], 0.70710677F * q0[1] + 0.70710677F * q0[3], 0.70710677F * q0[0] + -0.70710677F * q0[2], 0.70710677F * q0[1] + -0.70710677F * q0[3]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{0.70710677F * q0[0] + 0.70710677F * q0[1], 0.70710677F * q0[0] + -0.70710677F * q0[1], 0.70710677F * q0[2] + 0.70710677F * q0[3], 0.70710677F * q0[2] + -0.70710677F * q0[3]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    boolean $$_tmp_measureVar1;
    if (q0[2] * q0[2] + q1[2] * q1[2] + q0[3] * q0[3] + q1[3] * q1[3] > q0[0] * q0[0] + q1[0] * q1[0] + q0[1] * q0[1] + q1[1] * q1[1]) {
      q0 = new float[]{0.0F, 0.0F, q0[2], q0[3]};
      q1 = new float[]{0.0F, 0.0F, q1[2], q1[3]};
      $$_tmp_measureVar1 = true;
    } else {
      q0 = new float[]{q0[0], q0[1], 0.0F, 0.0F};
      q1 = new float[]{q1[0], q1[1], 0.0F, 0.0F};
      $$_tmp_measureVar1 = false;
    }
    boolean res1 = $$_tmp_measureVar1;
    boolean $$_tmp_measureVar2;
    if (q0[1] * q0[1] + q1[1] * q1[1] + q0[3] * q0[3] + q1[3] * q1[3] > q0[0] * q0[0] + q1[0] * q1[0] + q0[2] * q0[2] + q1[2] * q1[2]) {
      q0 = new float[]{0.0F, q0[1], 0.0F, q0[3]};
      q1 = new float[]{0.0F, q1[1], 0.0F, q1[3]};
      $$_tmp_measureVar2 = true;
    } else {
      q0 = new float[]{q0[0], 0.0F, q0[2], 0.0F};
      q1 = new float[]{q1[0], 0.0F, q1[2], 0.0F};
      $$_tmp_measureVar2 = false;
    }
    boolean res2 = $$_tmp_measureVar2;
    return (res1 ? 2 : 0) + (res2 ? 1 : 0);
  }
    /*@
      requires database != null && database.length == 4;
      requires (\forall int i; 0 <= i < 4; database[i] >= 0 && database[i] < 4);
      requires (\forall int i; 0 <= i < 4; (\forall int j; 0 <= j < 4; i == j || database[i] != database[j]));
      ensures ((val >= 0 && val < 4) ==> val == database[\result]);
      ensures ((val < 0 || val > 3) ==> \result == -1);
   */

  public static int grover2broken(/*@ non_null */
      int[] database, int val) {
    if (val < 0 || val > 3) {
      return -1;
    }
    /*@ non_null */
    final float[][] oracle2 = new float[][]{new float[]{val == database[0] ? 1.0F : -1.0F, 0.0F, 0.0F, 0.0F}, new float[]{0.0F, val == database[1] ? 1.0F : -1.0F, 0.0F, 0.0F}, new float[]{0.0F, 0.0F, val == database[2] ? 1.0F : -1.0F, 0.0F}, new float[]{0.0F, 0.0F, 0.0F, val == database[3] ? 1.0F : -1.0F}};
    float[] q0 = new float[]{1.0F, 0.0F, 0.0F, 0.0F};
    float[] q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{0.70710677F, 0.0F, 0.70710677F, 0.0F};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{0.49999997F, 0.49999997F, 0.49999997F, 0.49999997F};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{0.49999997F * oracle2[0][0] + 0.49999997F * oracle2[0][1], 0.49999997F * oracle2[0][0] + 0.49999997F * oracle2[0][1], 0.49999997F * oracle2[1][0] + 0.49999997F * oracle2[1][1], 0.49999997F * oracle2[1][0] + 0.49999997F * oracle2[1][1]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{0.70710677F * q0[0] + 0.70710677F * q0[2], 0.70710677F * q0[1] + 0.70710677F * q0[3], 0.70710677F * q0[0] + -0.70710677F * q0[2], 0.70710677F * q0[1] + -0.70710677F * q0[3]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{0.70710677F * q0[0] + 0.70710677F * q0[1], 0.70710677F * q0[0] + -0.70710677F * q0[1], 0.70710677F * q0[2] + 0.70710677F * q0[3], 0.70710677F * q0[2] + -0.70710677F * q0[3]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{q0[0], q0[1], -1.0F * q0[2], -1.0F * q0[3]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{q0[0], -1.0F * q0[1], q0[2], -1.0F * q0[3]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{q0[0], q0[1], q0[2], -1.0F * q0[3]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    q0 = new float[]{0.70710677F * q0[0] + 0.70710677F * q0[2], 0.70710677F * q0[1] + 0.70710677F * q0[3], 0.70710677F * q0[0] + -0.70710677F * q0[2], 0.70710677F * q0[1] + -0.70710677F * q0[3]};
    q1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F};
    boolean $$_tmp_measureVar3;
    if (q0[2] * q0[2] + q1[2] * q1[2] + q0[3] * q0[3] + q1[3] * q1[3] > q0[0] * q0[0] + q1[0] * q1[0] + q0[1] * q0[1] + q1[1] * q1[1]) {
      q0 = new float[]{0.0F, 0.0F, q0[2], q0[3]};
      q1 = new float[]{0.0F, 0.0F, q1[2], q1[3]};
      $$_tmp_measureVar3 = true;
    } else {
      q0 = new float[]{q0[0], q0[1], 0.0F, 0.0F};
      q1 = new float[]{q1[0], q1[1], 0.0F, 0.0F};
      $$_tmp_measureVar3 = false;
    }
    boolean res1 = $$_tmp_measureVar3;
    boolean $$_tmp_measureVar4;
    if (q0[1] * q0[1] + q1[1] * q1[1] + q0[3] * q0[3] + q1[3] * q1[3] > q0[0] * q0[0] + q1[0] * q1[0] + q0[2] * q0[2] + q1[2] * q1[2]) {
      q0 = new float[]{0.0F, q0[1], 0.0F, q0[3]};
      q1 = new float[]{0.0F, q1[1], 0.0F, q1[3]};
      $$_tmp_measureVar4 = true;
    } else {
      q0 = new float[]{q0[0], 0.0F, q0[2], 0.0F};
      q1 = new float[]{q1[0], 0.0F, q1[2], 0.0F};
      $$_tmp_measureVar4 = false;
    }
    boolean res2 = $$_tmp_measureVar4;
    return (res1 ? 2 : 0) + (res2 ? 1 : 0);
  }
}
