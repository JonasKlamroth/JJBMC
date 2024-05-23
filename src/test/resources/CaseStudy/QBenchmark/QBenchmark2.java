
public class QBenchmark2S {

    public QBenchmark2S() {
        super();
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\forall int i; i >= 0 && i < qstate.length; qstate[i] != null && qstatei[i] != null && qstate[i].length == 1 && qstatei[i].length == 1);
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i][0] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j][0] == 0.0F));
      requires (\exists int i; i >= 0 && i < qstate.length; qstatei[i][0] == 0.0F);
   */

    public static void gatesTest_1_1(/*@ non_null */
            float[][] qstate, /*@ non_null */
            float[][] qstatei) {
        boolean b_test = qstate[0][0] != 0.0F;
        float[][] q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        float[][] q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        boolean $$_tmp_measureVar1;
        if ((q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) * (q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) > (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0]) * (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0])) {
            q_state_0 = new float[][]{new float[]{0.0F}, new float[]{q_state_0[1][0]}};
            q_state_1 = new float[][]{new float[]{0.0F}, new float[]{q_state_1[1][0]}};
            $$_tmp_measureVar1 = true;
        } else {
            q_state_0 = new float[][]{new float[]{q_state_0[0][0]}, new float[]{0.0F}};
            q_state_1 = new float[][]{new float[]{q_state_1[0][0]}, new float[]{0.0F}};
            $$_tmp_measureVar1 = false;
        }
        boolean b_0 = $$_tmp_measureVar1;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\forall int i; i >= 0 && i < qstate.length; qstate[i] != null && qstatei[i] != null && qstate[i].length == 1 && qstatei[i].length == 1);
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i][0] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j][0] == 0.0F));
      requires (\exists int i; i >= 0 && i < qstate.length; qstatei[i][0] == 0.0F);
   */

    public static void gatesTest_1_2(/*@ non_null */
            float[][] qstate, /*@ non_null */
            float[][] qstatei) {
        boolean b_test_0 = qstate[0][0] == 1.0F;
        float[][] q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        float[][] q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
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
        boolean b_0 = $$_tmp_measureVar2;
        assert b_0 == b_test_0;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\forall int i; i >= 0 && i < qstate.length; qstate[i] != null && qstatei[i] != null && qstate[i].length == 1 && qstatei[i].length == 1);
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i][0] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j][0] == 0.0F));
      requires (\exists int i; i >= 0 && i < qstate.length; qstatei[i][0] == 0.0F);
   */

    public static void gatesTest_1_3(/*@ non_null */
            float[][] qstate, /*@ non_null */
            float[][] qstatei) {
        boolean b_test_0 = qstate[0][0] == 1.0F;
        float[][] q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        float[][] q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        boolean $$_tmp_measureVar3;
        if ((q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) * (q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) > (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0]) * (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0])) {
            q_state_0 = new float[][]{new float[]{0.0F}, new float[]{q_state_0[1][0]}};
            q_state_1 = new float[][]{new float[]{0.0F}, new float[]{q_state_1[1][0]}};
            $$_tmp_measureVar3 = true;
        } else {
            q_state_0 = new float[][]{new float[]{q_state_0[0][0]}, new float[]{0.0F}};
            q_state_1 = new float[][]{new float[]{q_state_1[0][0]}, new float[]{0.0F}};
            $$_tmp_measureVar3 = false;
        }
        boolean b_0 = $$_tmp_measureVar3;
        assert b_0 != b_test_0;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\forall int i; i >= 0 && i < qstate.length; qstate[i] != null && qstatei[i] != null && qstate[i].length == 1 && qstatei[i].length == 1);
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i][0] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j][0] == 0.0F));
      requires (\exists int i; i >= 0 && i < qstate.length; qstatei[i][0] == 0.0F);
   */

    public static void gatesTest_1_4(/*@ non_null */
            float[][] qstate, /*@ non_null */
            float[][] qstatei) {
        boolean b_test_0 = qstate[0][0] == 1.0F;
        float[][] q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        float[][] q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        boolean $$_tmp_measureVar4;
        if ((q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) * (q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) > (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0]) * (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0])) {
            q_state_0 = new float[][]{new float[]{0.0F}, new float[]{q_state_0[1][0]}};
            q_state_1 = new float[][]{new float[]{0.0F}, new float[]{q_state_1[1][0]}};
            $$_tmp_measureVar4 = true;
        } else {
            q_state_0 = new float[][]{new float[]{q_state_0[0][0]}, new float[]{0.0F}};
            q_state_1 = new float[][]{new float[]{q_state_1[0][0]}, new float[]{0.0F}};
            $$_tmp_measureVar4 = false;
        }
        boolean b_0 = $$_tmp_measureVar4;
        assert b_0 == b_test_0;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\forall int i; i >= 0 && i < qstate.length; qstate[i] != null && qstatei[i] != null && qstate[i].length == 1 && qstatei[i].length == 1);
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i][0] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j][0] == 0.0F));
      requires (\exists int i; i >= 0 && i < qstate.length; qstatei[i][0] == 0.0F);
   */

    public static void gatesTest_1_5(/*@ non_null */
            float[][] qstate, /*@ non_null */
            float[][] qstatei) {
        boolean b_test_0 = qstate[0][0] == 1.0F;
        float[][] q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        float[][] q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        boolean $$_tmp_measureVar5;
        if ((q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) * (q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) > (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0]) * (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0])) {
            q_state_0 = new float[][]{new float[]{0.0F}, new float[]{q_state_0[1][0]}};
            q_state_1 = new float[][]{new float[]{0.0F}, new float[]{q_state_1[1][0]}};
            $$_tmp_measureVar5 = true;
        } else {
            q_state_0 = new float[][]{new float[]{q_state_0[0][0]}, new float[]{0.0F}};
            q_state_1 = new float[][]{new float[]{q_state_1[0][0]}, new float[]{0.0F}};
            $$_tmp_measureVar5 = false;
        }
        boolean b_0 = $$_tmp_measureVar5;
        assert b_0 != b_test_0;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\forall int i; i >= 0 && i < qstate.length; qstate[i] != null && qstatei[i] != null && qstate[i].length == 1 && qstatei[i].length == 1);
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i][0] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j][0] == 0.0F));
      requires (\exists int i; i >= 0 && i < qstate.length; qstatei[i][0] == 0.0F);
   */

    public static void gatesTest_1_6(/*@ non_null */
            float[][] qstate, /*@ non_null */
            float[][] qstatei) {
        boolean b_test_0 = qstate[0][0] == 1.0F;
        float[][] q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        float[][] q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        boolean $$_tmp_measureVar6;
        if ((q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) * (q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) > (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0]) * (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0])) {
            q_state_0 = new float[][]{new float[]{0.0F}, new float[]{q_state_0[1][0]}};
            q_state_1 = new float[][]{new float[]{0.0F}, new float[]{q_state_1[1][0]}};
            $$_tmp_measureVar6 = true;
        } else {
            q_state_0 = new float[][]{new float[]{q_state_0[0][0]}, new float[]{0.0F}};
            q_state_1 = new float[][]{new float[]{q_state_1[0][0]}, new float[]{0.0F}};
            $$_tmp_measureVar6 = false;
        }
        boolean b_0 = $$_tmp_measureVar6;
        assert b_0 == b_test_0;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\forall int i; i >= 0 && i < qstate.length; qstate[i] != null && qstatei[i] != null && qstate[i].length == 1 && qstatei[i].length == 1);
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i][0] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j][0] == 0.0F));
      requires (\exists int i; i >= 0 && i < qstate.length; qstatei[i][0] == 0.0F);
   */

    public static void gatesTest_1_7(/*@ non_null */
            float[][] qstate, /*@ non_null */
            float[][] qstatei) {
        boolean b_test_0 = qstate[0][0] == 1.0F;
        float[][] q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        float[][] q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        q_state_0 = new float[][]{new float[]{qstate[0][0]}, new float[]{qstate[1][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[0][0]}, new float[]{qstatei[1][0]}};
        q_state_0 = new float[][]{new float[]{qstate[1][0]}, new float[]{qstate[0][0]}};
        q_state_1 = new float[][]{new float[]{qstatei[1][0]}, new float[]{qstatei[0][0]}};
        boolean $$_tmp_measureVar7;
        if ((q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) * (q_state_0[1][0] * q_state_0[1][0] + q_state_1[1][0] * q_state_1[1][0]) > (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0]) * (q_state_0[0][0] * q_state_0[0][0] + q_state_1[0][0] * q_state_1[0][0])) {
            q_state_0 = new float[][]{new float[]{0.0F}, new float[]{q_state_0[1][0]}};
            q_state_1 = new float[][]{new float[]{0.0F}, new float[]{q_state_1[1][0]}};
            $$_tmp_measureVar7 = true;
        } else {
            q_state_0 = new float[][]{new float[]{q_state_0[0][0]}, new float[]{0.0F}};
            q_state_1 = new float[][]{new float[]{q_state_1[0][0]}, new float[]{0.0F}};
            $$_tmp_measureVar7 = false;
        }
        boolean b_0 = $$_tmp_measureVar7;
        assert b_0 != b_test_0;
    }
}
