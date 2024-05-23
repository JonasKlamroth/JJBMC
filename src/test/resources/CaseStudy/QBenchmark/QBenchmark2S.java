
public class QBenchmark2S {

    public QBenchmark2S() {
        super();
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_1_1(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 1; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        boolean $$_tmp_measureVar1;
        if (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) {
            q_state_0 = new float[]{0.0F, q_state_0[1]};
            q_state_1 = new float[]{0.0F, q_state_1[1]};
            $$_tmp_measureVar1 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F};
            $$_tmp_measureVar1 = false;
        }
        boolean b_0 = $$_tmp_measureVar1;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_1_2(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 1; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        boolean $$_tmp_measureVar2;
        if (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) {
            q_state_0 = new float[]{0.0F, q_state_0[1]};
            q_state_1 = new float[]{0.0F, q_state_1[1]};
            $$_tmp_measureVar2 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F};
            $$_tmp_measureVar2 = false;
        }
        boolean b_0 = $$_tmp_measureVar2;
        assert b_0 == b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_1_3(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 1; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        boolean $$_tmp_measureVar3;
        if (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) {
            q_state_0 = new float[]{0.0F, q_state_0[1]};
            q_state_1 = new float[]{0.0F, q_state_1[1]};
            $$_tmp_measureVar3 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F};
            $$_tmp_measureVar3 = false;
        }
        boolean b_0 = $$_tmp_measureVar3;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_1_4(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 1; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        boolean $$_tmp_measureVar4;
        if (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) {
            q_state_0 = new float[]{0.0F, q_state_0[1]};
            q_state_1 = new float[]{0.0F, q_state_1[1]};
            $$_tmp_measureVar4 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F};
            $$_tmp_measureVar4 = false;
        }
        boolean b_0 = $$_tmp_measureVar4;
        assert b_0 == b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_1_5(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 1; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        boolean $$_tmp_measureVar5;
        if (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) {
            q_state_0 = new float[]{0.0F, q_state_0[1]};
            q_state_1 = new float[]{0.0F, q_state_1[1]};
            $$_tmp_measureVar5 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F};
            $$_tmp_measureVar5 = false;
        }
        boolean b_0 = $$_tmp_measureVar5;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_1_6(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 1; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        boolean $$_tmp_measureVar6;
        if (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) {
            q_state_0 = new float[]{0.0F, q_state_0[1]};
            q_state_1 = new float[]{0.0F, q_state_1[1]};
            $$_tmp_measureVar6 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F};
            $$_tmp_measureVar6 = false;
        }
        boolean b_0 = $$_tmp_measureVar6;
        assert b_0 == b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_1_7(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 1; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        boolean $$_tmp_measureVar7;
        if (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) {
            q_state_0 = new float[]{0.0F, q_state_0[1]};
            q_state_1 = new float[]{0.0F, q_state_1[1]};
            $$_tmp_measureVar7 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F};
            $$_tmp_measureVar7 = false;
        }
        boolean b_0 = $$_tmp_measureVar7;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_1_8(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 1; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        boolean $$_tmp_measureVar8;
        if (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) {
            q_state_0 = new float[]{0.0F, q_state_0[1]};
            q_state_1 = new float[]{0.0F, q_state_1[1]};
            $$_tmp_measureVar8 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F};
            $$_tmp_measureVar8 = false;
        }
        boolean b_0 = $$_tmp_measureVar8;
        assert b_0 == b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 2 && qstatei.length == 2;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_1_9(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 1; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        q_state_0 = new float[]{q_state_0[1], q_state_0[0]};
        q_state_1 = new float[]{q_state_1[1], q_state_1[0]};
        boolean $$_tmp_measureVar9;
        if (q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0]) {
            q_state_0 = new float[]{0.0F, q_state_0[1]};
            q_state_1 = new float[]{0.0F, q_state_1[1]};
            $$_tmp_measureVar9 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], 0.0F};
            q_state_1 = new float[]{q_state_1[0], 0.0F};
            $$_tmp_measureVar9 = false;
        }
        boolean b_0 = $$_tmp_measureVar9;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 8 && qstatei.length == 8;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_3_1(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 4; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        boolean $$_tmp_measureVar10;
        if (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7]};
            $$_tmp_measureVar10 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar10 = false;
        }
        boolean b_0 = $$_tmp_measureVar10;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 8 && qstatei.length == 8;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_3_2(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 4; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        boolean $$_tmp_measureVar11;
        if (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7]};
            $$_tmp_measureVar11 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar11 = false;
        }
        boolean b_0 = $$_tmp_measureVar11;
        assert b_0 == b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 8 && qstatei.length == 8;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_3_3(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 4; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        boolean $$_tmp_measureVar12;
        if (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7]};
            $$_tmp_measureVar12 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar12 = false;
        }
        boolean b_0 = $$_tmp_measureVar12;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 8 && qstatei.length == 8;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_3_4(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 4; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        boolean $$_tmp_measureVar13;
        if (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7]};
            $$_tmp_measureVar13 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar13 = false;
        }
        boolean b_0 = $$_tmp_measureVar13;
        assert b_0 == b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 8 && qstatei.length == 8;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_3_5(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 4; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        boolean $$_tmp_measureVar14;
        if (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7]};
            $$_tmp_measureVar14 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar14 = false;
        }
        boolean b_0 = $$_tmp_measureVar14;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 8 && qstatei.length == 8;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_3_6(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 4; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        boolean $$_tmp_measureVar15;
        if (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7]};
            $$_tmp_measureVar15 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar15 = false;
        }
        boolean b_0 = $$_tmp_measureVar15;
        assert b_0 == b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 8 && qstatei.length == 8;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_3_7(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 4; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        boolean $$_tmp_measureVar16;
        if (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7]};
            $$_tmp_measureVar16 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar16 = false;
        }
        boolean b_0 = $$_tmp_measureVar16;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 8 && qstatei.length == 8;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_3_8(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 4; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        boolean $$_tmp_measureVar17;
        if (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7]};
            $$_tmp_measureVar17 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar17 = false;
        }
        boolean b_0 = $$_tmp_measureVar17;
        assert b_0 == b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 8 && qstatei.length == 8;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_3_9(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 4; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        q_state_0 = new float[]{q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3]};
        q_state_1 = new float[]{q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3]};
        boolean $$_tmp_measureVar18;
        if (q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7]};
            $$_tmp_measureVar18 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar18 = false;
        }
        boolean b_0 = $$_tmp_measureVar18;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 32 && qstatei.length == 32;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_5_1(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 16; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7], qstate[8], qstate[9], qstate[10], qstate[11], qstate[12], qstate[13], qstate[14], qstate[15], qstate[16], qstate[17], qstate[18], qstate[19], qstate[20], qstate[21], qstate[22], qstate[23], qstate[24], qstate[25], qstate[26], qstate[27], qstate[28], qstate[29], qstate[30], qstate[31]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7], qstatei[8], qstatei[9], qstatei[10], qstatei[11], qstatei[12], qstatei[13], qstatei[14], qstatei[15], qstatei[16], qstatei[17], qstatei[18], qstatei[19], qstatei[20], qstatei[21], qstatei[22], qstatei[23], qstatei[24], qstatei[25], qstatei[26], qstatei[27], qstatei[28], qstatei[29], qstatei[30], qstatei[31]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        boolean $$_tmp_measureVar19;
        if (q_state_0[16] * q_state_0[16] + q_state_1[16] * q_state_1[16] + q_state_0[17] * q_state_0[17] + q_state_1[17] * q_state_1[17] + q_state_0[18] * q_state_0[18] + q_state_1[18] * q_state_1[18] + q_state_0[19] * q_state_0[19] + q_state_1[19] * q_state_1[19] + q_state_0[20] * q_state_0[20] + q_state_1[20] * q_state_1[20] + q_state_0[21] * q_state_0[21] + q_state_1[21] * q_state_1[21] + q_state_0[22] * q_state_0[22] + q_state_1[22] * q_state_1[22] + q_state_0[23] * q_state_0[23] + q_state_1[23] * q_state_1[23] + q_state_0[24] * q_state_0[24] + q_state_1[24] * q_state_1[24] + q_state_0[25] * q_state_0[25] + q_state_1[25] * q_state_1[25] + q_state_0[26] * q_state_0[26] + q_state_1[26] * q_state_1[26] + q_state_0[27] * q_state_0[27] + q_state_1[27] * q_state_1[27] + q_state_0[28] * q_state_0[28] + q_state_1[28] * q_state_1[28] + q_state_0[29] * q_state_0[29] + q_state_1[29] * q_state_1[29] + q_state_0[30] * q_state_0[30] + q_state_1[30] * q_state_1[30] + q_state_0[31] * q_state_0[31] + q_state_1[31] * q_state_1[31] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3] + q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] + q_state_0[8] * q_state_0[8] + q_state_1[8] * q_state_1[8] + q_state_0[9] * q_state_0[9] + q_state_1[9] * q_state_1[9] + q_state_0[10] * q_state_0[10] + q_state_1[10] * q_state_1[10] + q_state_0[11] * q_state_0[11] + q_state_1[11] * q_state_1[11] + q_state_0[12] * q_state_0[12] + q_state_1[12] * q_state_1[12] + q_state_0[13] * q_state_0[13] + q_state_1[13] * q_state_1[13] + q_state_0[14] * q_state_0[14] + q_state_1[14] * q_state_1[14] + q_state_0[15] * q_state_0[15] + q_state_1[15] * q_state_1[15]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31]};
            $$_tmp_measureVar19 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar19 = false;
        }
        boolean b_0 = $$_tmp_measureVar19;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 32 && qstatei.length == 32;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_5_2(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 16; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7], qstate[8], qstate[9], qstate[10], qstate[11], qstate[12], qstate[13], qstate[14], qstate[15], qstate[16], qstate[17], qstate[18], qstate[19], qstate[20], qstate[21], qstate[22], qstate[23], qstate[24], qstate[25], qstate[26], qstate[27], qstate[28], qstate[29], qstate[30], qstate[31]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7], qstatei[8], qstatei[9], qstatei[10], qstatei[11], qstatei[12], qstatei[13], qstatei[14], qstatei[15], qstatei[16], qstatei[17], qstatei[18], qstatei[19], qstatei[20], qstatei[21], qstatei[22], qstatei[23], qstatei[24], qstatei[25], qstatei[26], qstatei[27], qstatei[28], qstatei[29], qstatei[30], qstatei[31]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        boolean $$_tmp_measureVar20;
        if (q_state_0[16] * q_state_0[16] + q_state_1[16] * q_state_1[16] + q_state_0[17] * q_state_0[17] + q_state_1[17] * q_state_1[17] + q_state_0[18] * q_state_0[18] + q_state_1[18] * q_state_1[18] + q_state_0[19] * q_state_0[19] + q_state_1[19] * q_state_1[19] + q_state_0[20] * q_state_0[20] + q_state_1[20] * q_state_1[20] + q_state_0[21] * q_state_0[21] + q_state_1[21] * q_state_1[21] + q_state_0[22] * q_state_0[22] + q_state_1[22] * q_state_1[22] + q_state_0[23] * q_state_0[23] + q_state_1[23] * q_state_1[23] + q_state_0[24] * q_state_0[24] + q_state_1[24] * q_state_1[24] + q_state_0[25] * q_state_0[25] + q_state_1[25] * q_state_1[25] + q_state_0[26] * q_state_0[26] + q_state_1[26] * q_state_1[26] + q_state_0[27] * q_state_0[27] + q_state_1[27] * q_state_1[27] + q_state_0[28] * q_state_0[28] + q_state_1[28] * q_state_1[28] + q_state_0[29] * q_state_0[29] + q_state_1[29] * q_state_1[29] + q_state_0[30] * q_state_0[30] + q_state_1[30] * q_state_1[30] + q_state_0[31] * q_state_0[31] + q_state_1[31] * q_state_1[31] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3] + q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] + q_state_0[8] * q_state_0[8] + q_state_1[8] * q_state_1[8] + q_state_0[9] * q_state_0[9] + q_state_1[9] * q_state_1[9] + q_state_0[10] * q_state_0[10] + q_state_1[10] * q_state_1[10] + q_state_0[11] * q_state_0[11] + q_state_1[11] * q_state_1[11] + q_state_0[12] * q_state_0[12] + q_state_1[12] * q_state_1[12] + q_state_0[13] * q_state_0[13] + q_state_1[13] * q_state_1[13] + q_state_0[14] * q_state_0[14] + q_state_1[14] * q_state_1[14] + q_state_0[15] * q_state_0[15] + q_state_1[15] * q_state_1[15]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31]};
            $$_tmp_measureVar20 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar20 = false;
        }
        boolean b_0 = $$_tmp_measureVar20;
        assert b_0 == b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 32 && qstatei.length == 32;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_5_3(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 16; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7], qstate[8], qstate[9], qstate[10], qstate[11], qstate[12], qstate[13], qstate[14], qstate[15], qstate[16], qstate[17], qstate[18], qstate[19], qstate[20], qstate[21], qstate[22], qstate[23], qstate[24], qstate[25], qstate[26], qstate[27], qstate[28], qstate[29], qstate[30], qstate[31]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7], qstatei[8], qstatei[9], qstatei[10], qstatei[11], qstatei[12], qstatei[13], qstatei[14], qstatei[15], qstatei[16], qstatei[17], qstatei[18], qstatei[19], qstatei[20], qstatei[21], qstatei[22], qstatei[23], qstatei[24], qstatei[25], qstatei[26], qstatei[27], qstatei[28], qstatei[29], qstatei[30], qstatei[31]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        boolean $$_tmp_measureVar21;
        if (q_state_0[16] * q_state_0[16] + q_state_1[16] * q_state_1[16] + q_state_0[17] * q_state_0[17] + q_state_1[17] * q_state_1[17] + q_state_0[18] * q_state_0[18] + q_state_1[18] * q_state_1[18] + q_state_0[19] * q_state_0[19] + q_state_1[19] * q_state_1[19] + q_state_0[20] * q_state_0[20] + q_state_1[20] * q_state_1[20] + q_state_0[21] * q_state_0[21] + q_state_1[21] * q_state_1[21] + q_state_0[22] * q_state_0[22] + q_state_1[22] * q_state_1[22] + q_state_0[23] * q_state_0[23] + q_state_1[23] * q_state_1[23] + q_state_0[24] * q_state_0[24] + q_state_1[24] * q_state_1[24] + q_state_0[25] * q_state_0[25] + q_state_1[25] * q_state_1[25] + q_state_0[26] * q_state_0[26] + q_state_1[26] * q_state_1[26] + q_state_0[27] * q_state_0[27] + q_state_1[27] * q_state_1[27] + q_state_0[28] * q_state_0[28] + q_state_1[28] * q_state_1[28] + q_state_0[29] * q_state_0[29] + q_state_1[29] * q_state_1[29] + q_state_0[30] * q_state_0[30] + q_state_1[30] * q_state_1[30] + q_state_0[31] * q_state_0[31] + q_state_1[31] * q_state_1[31] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3] + q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] + q_state_0[8] * q_state_0[8] + q_state_1[8] * q_state_1[8] + q_state_0[9] * q_state_0[9] + q_state_1[9] * q_state_1[9] + q_state_0[10] * q_state_0[10] + q_state_1[10] * q_state_1[10] + q_state_0[11] * q_state_0[11] + q_state_1[11] * q_state_1[11] + q_state_0[12] * q_state_0[12] + q_state_1[12] * q_state_1[12] + q_state_0[13] * q_state_0[13] + q_state_1[13] * q_state_1[13] + q_state_0[14] * q_state_0[14] + q_state_1[14] * q_state_1[14] + q_state_0[15] * q_state_0[15] + q_state_1[15] * q_state_1[15]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31]};
            $$_tmp_measureVar21 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar21 = false;
        }
        boolean b_0 = $$_tmp_measureVar21;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 32 && qstatei.length == 32;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_5_4(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 16; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7], qstate[8], qstate[9], qstate[10], qstate[11], qstate[12], qstate[13], qstate[14], qstate[15], qstate[16], qstate[17], qstate[18], qstate[19], qstate[20], qstate[21], qstate[22], qstate[23], qstate[24], qstate[25], qstate[26], qstate[27], qstate[28], qstate[29], qstate[30], qstate[31]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7], qstatei[8], qstatei[9], qstatei[10], qstatei[11], qstatei[12], qstatei[13], qstatei[14], qstatei[15], qstatei[16], qstatei[17], qstatei[18], qstatei[19], qstatei[20], qstatei[21], qstatei[22], qstatei[23], qstatei[24], qstatei[25], qstatei[26], qstatei[27], qstatei[28], qstatei[29], qstatei[30], qstatei[31]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        boolean $$_tmp_measureVar22;
        if (q_state_0[16] * q_state_0[16] + q_state_1[16] * q_state_1[16] + q_state_0[17] * q_state_0[17] + q_state_1[17] * q_state_1[17] + q_state_0[18] * q_state_0[18] + q_state_1[18] * q_state_1[18] + q_state_0[19] * q_state_0[19] + q_state_1[19] * q_state_1[19] + q_state_0[20] * q_state_0[20] + q_state_1[20] * q_state_1[20] + q_state_0[21] * q_state_0[21] + q_state_1[21] * q_state_1[21] + q_state_0[22] * q_state_0[22] + q_state_1[22] * q_state_1[22] + q_state_0[23] * q_state_0[23] + q_state_1[23] * q_state_1[23] + q_state_0[24] * q_state_0[24] + q_state_1[24] * q_state_1[24] + q_state_0[25] * q_state_0[25] + q_state_1[25] * q_state_1[25] + q_state_0[26] * q_state_0[26] + q_state_1[26] * q_state_1[26] + q_state_0[27] * q_state_0[27] + q_state_1[27] * q_state_1[27] + q_state_0[28] * q_state_0[28] + q_state_1[28] * q_state_1[28] + q_state_0[29] * q_state_0[29] + q_state_1[29] * q_state_1[29] + q_state_0[30] * q_state_0[30] + q_state_1[30] * q_state_1[30] + q_state_0[31] * q_state_0[31] + q_state_1[31] * q_state_1[31] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3] + q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] + q_state_0[8] * q_state_0[8] + q_state_1[8] * q_state_1[8] + q_state_0[9] * q_state_0[9] + q_state_1[9] * q_state_1[9] + q_state_0[10] * q_state_0[10] + q_state_1[10] * q_state_1[10] + q_state_0[11] * q_state_0[11] + q_state_1[11] * q_state_1[11] + q_state_0[12] * q_state_0[12] + q_state_1[12] * q_state_1[12] + q_state_0[13] * q_state_0[13] + q_state_1[13] * q_state_1[13] + q_state_0[14] * q_state_0[14] + q_state_1[14] * q_state_1[14] + q_state_0[15] * q_state_0[15] + q_state_1[15] * q_state_1[15]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31]};
            $$_tmp_measureVar22 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar22 = false;
        }
        boolean b_0 = $$_tmp_measureVar22;
        assert b_0 == b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 32 && qstatei.length == 32;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_5_5(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 16; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7], qstate[8], qstate[9], qstate[10], qstate[11], qstate[12], qstate[13], qstate[14], qstate[15], qstate[16], qstate[17], qstate[18], qstate[19], qstate[20], qstate[21], qstate[22], qstate[23], qstate[24], qstate[25], qstate[26], qstate[27], qstate[28], qstate[29], qstate[30], qstate[31]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7], qstatei[8], qstatei[9], qstatei[10], qstatei[11], qstatei[12], qstatei[13], qstatei[14], qstatei[15], qstatei[16], qstatei[17], qstatei[18], qstatei[19], qstatei[20], qstatei[21], qstatei[22], qstatei[23], qstatei[24], qstatei[25], qstatei[26], qstatei[27], qstatei[28], qstatei[29], qstatei[30], qstatei[31]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        boolean $$_tmp_measureVar23;
        if (q_state_0[16] * q_state_0[16] + q_state_1[16] * q_state_1[16] + q_state_0[17] * q_state_0[17] + q_state_1[17] * q_state_1[17] + q_state_0[18] * q_state_0[18] + q_state_1[18] * q_state_1[18] + q_state_0[19] * q_state_0[19] + q_state_1[19] * q_state_1[19] + q_state_0[20] * q_state_0[20] + q_state_1[20] * q_state_1[20] + q_state_0[21] * q_state_0[21] + q_state_1[21] * q_state_1[21] + q_state_0[22] * q_state_0[22] + q_state_1[22] * q_state_1[22] + q_state_0[23] * q_state_0[23] + q_state_1[23] * q_state_1[23] + q_state_0[24] * q_state_0[24] + q_state_1[24] * q_state_1[24] + q_state_0[25] * q_state_0[25] + q_state_1[25] * q_state_1[25] + q_state_0[26] * q_state_0[26] + q_state_1[26] * q_state_1[26] + q_state_0[27] * q_state_0[27] + q_state_1[27] * q_state_1[27] + q_state_0[28] * q_state_0[28] + q_state_1[28] * q_state_1[28] + q_state_0[29] * q_state_0[29] + q_state_1[29] * q_state_1[29] + q_state_0[30] * q_state_0[30] + q_state_1[30] * q_state_1[30] + q_state_0[31] * q_state_0[31] + q_state_1[31] * q_state_1[31] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3] + q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] + q_state_0[8] * q_state_0[8] + q_state_1[8] * q_state_1[8] + q_state_0[9] * q_state_0[9] + q_state_1[9] * q_state_1[9] + q_state_0[10] * q_state_0[10] + q_state_1[10] * q_state_1[10] + q_state_0[11] * q_state_0[11] + q_state_1[11] * q_state_1[11] + q_state_0[12] * q_state_0[12] + q_state_1[12] * q_state_1[12] + q_state_0[13] * q_state_0[13] + q_state_1[13] * q_state_1[13] + q_state_0[14] * q_state_0[14] + q_state_1[14] * q_state_1[14] + q_state_0[15] * q_state_0[15] + q_state_1[15] * q_state_1[15]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31]};
            $$_tmp_measureVar23 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar23 = false;
        }
        boolean b_0 = $$_tmp_measureVar23;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 32 && qstatei.length == 32;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_5_6(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 16; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7], qstate[8], qstate[9], qstate[10], qstate[11], qstate[12], qstate[13], qstate[14], qstate[15], qstate[16], qstate[17], qstate[18], qstate[19], qstate[20], qstate[21], qstate[22], qstate[23], qstate[24], qstate[25], qstate[26], qstate[27], qstate[28], qstate[29], qstate[30], qstate[31]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7], qstatei[8], qstatei[9], qstatei[10], qstatei[11], qstatei[12], qstatei[13], qstatei[14], qstatei[15], qstatei[16], qstatei[17], qstatei[18], qstatei[19], qstatei[20], qstatei[21], qstatei[22], qstatei[23], qstatei[24], qstatei[25], qstatei[26], qstatei[27], qstatei[28], qstatei[29], qstatei[30], qstatei[31]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        boolean $$_tmp_measureVar24;
        if (q_state_0[16] * q_state_0[16] + q_state_1[16] * q_state_1[16] + q_state_0[17] * q_state_0[17] + q_state_1[17] * q_state_1[17] + q_state_0[18] * q_state_0[18] + q_state_1[18] * q_state_1[18] + q_state_0[19] * q_state_0[19] + q_state_1[19] * q_state_1[19] + q_state_0[20] * q_state_0[20] + q_state_1[20] * q_state_1[20] + q_state_0[21] * q_state_0[21] + q_state_1[21] * q_state_1[21] + q_state_0[22] * q_state_0[22] + q_state_1[22] * q_state_1[22] + q_state_0[23] * q_state_0[23] + q_state_1[23] * q_state_1[23] + q_state_0[24] * q_state_0[24] + q_state_1[24] * q_state_1[24] + q_state_0[25] * q_state_0[25] + q_state_1[25] * q_state_1[25] + q_state_0[26] * q_state_0[26] + q_state_1[26] * q_state_1[26] + q_state_0[27] * q_state_0[27] + q_state_1[27] * q_state_1[27] + q_state_0[28] * q_state_0[28] + q_state_1[28] * q_state_1[28] + q_state_0[29] * q_state_0[29] + q_state_1[29] * q_state_1[29] + q_state_0[30] * q_state_0[30] + q_state_1[30] * q_state_1[30] + q_state_0[31] * q_state_0[31] + q_state_1[31] * q_state_1[31] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3] + q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] + q_state_0[8] * q_state_0[8] + q_state_1[8] * q_state_1[8] + q_state_0[9] * q_state_0[9] + q_state_1[9] * q_state_1[9] + q_state_0[10] * q_state_0[10] + q_state_1[10] * q_state_1[10] + q_state_0[11] * q_state_0[11] + q_state_1[11] * q_state_1[11] + q_state_0[12] * q_state_0[12] + q_state_1[12] * q_state_1[12] + q_state_0[13] * q_state_0[13] + q_state_1[13] * q_state_1[13] + q_state_0[14] * q_state_0[14] + q_state_1[14] * q_state_1[14] + q_state_0[15] * q_state_0[15] + q_state_1[15] * q_state_1[15]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31]};
            $$_tmp_measureVar24 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar24 = false;
        }
        boolean b_0 = $$_tmp_measureVar24;
        assert b_0 == b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 32 && qstatei.length == 32;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_5_7(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 16; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7], qstate[8], qstate[9], qstate[10], qstate[11], qstate[12], qstate[13], qstate[14], qstate[15], qstate[16], qstate[17], qstate[18], qstate[19], qstate[20], qstate[21], qstate[22], qstate[23], qstate[24], qstate[25], qstate[26], qstate[27], qstate[28], qstate[29], qstate[30], qstate[31]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7], qstatei[8], qstatei[9], qstatei[10], qstatei[11], qstatei[12], qstatei[13], qstatei[14], qstatei[15], qstatei[16], qstatei[17], qstatei[18], qstatei[19], qstatei[20], qstatei[21], qstatei[22], qstatei[23], qstatei[24], qstatei[25], qstatei[26], qstatei[27], qstatei[28], qstatei[29], qstatei[30], qstatei[31]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        boolean $$_tmp_measureVar25;
        if (q_state_0[16] * q_state_0[16] + q_state_1[16] * q_state_1[16] + q_state_0[17] * q_state_0[17] + q_state_1[17] * q_state_1[17] + q_state_0[18] * q_state_0[18] + q_state_1[18] * q_state_1[18] + q_state_0[19] * q_state_0[19] + q_state_1[19] * q_state_1[19] + q_state_0[20] * q_state_0[20] + q_state_1[20] * q_state_1[20] + q_state_0[21] * q_state_0[21] + q_state_1[21] * q_state_1[21] + q_state_0[22] * q_state_0[22] + q_state_1[22] * q_state_1[22] + q_state_0[23] * q_state_0[23] + q_state_1[23] * q_state_1[23] + q_state_0[24] * q_state_0[24] + q_state_1[24] * q_state_1[24] + q_state_0[25] * q_state_0[25] + q_state_1[25] * q_state_1[25] + q_state_0[26] * q_state_0[26] + q_state_1[26] * q_state_1[26] + q_state_0[27] * q_state_0[27] + q_state_1[27] * q_state_1[27] + q_state_0[28] * q_state_0[28] + q_state_1[28] * q_state_1[28] + q_state_0[29] * q_state_0[29] + q_state_1[29] * q_state_1[29] + q_state_0[30] * q_state_0[30] + q_state_1[30] * q_state_1[30] + q_state_0[31] * q_state_0[31] + q_state_1[31] * q_state_1[31] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3] + q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] + q_state_0[8] * q_state_0[8] + q_state_1[8] * q_state_1[8] + q_state_0[9] * q_state_0[9] + q_state_1[9] * q_state_1[9] + q_state_0[10] * q_state_0[10] + q_state_1[10] * q_state_1[10] + q_state_0[11] * q_state_0[11] + q_state_1[11] * q_state_1[11] + q_state_0[12] * q_state_0[12] + q_state_1[12] * q_state_1[12] + q_state_0[13] * q_state_0[13] + q_state_1[13] * q_state_1[13] + q_state_0[14] * q_state_0[14] + q_state_1[14] * q_state_1[14] + q_state_0[15] * q_state_0[15] + q_state_1[15] * q_state_1[15]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31]};
            $$_tmp_measureVar25 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar25 = false;
        }
        boolean b_0 = $$_tmp_measureVar25;
        assert b_0 != b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 32 && qstatei.length == 32;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_5_8(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 16; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7], qstate[8], qstate[9], qstate[10], qstate[11], qstate[12], qstate[13], qstate[14], qstate[15], qstate[16], qstate[17], qstate[18], qstate[19], qstate[20], qstate[21], qstate[22], qstate[23], qstate[24], qstate[25], qstate[26], qstate[27], qstate[28], qstate[29], qstate[30], qstate[31]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7], qstatei[8], qstatei[9], qstatei[10], qstatei[11], qstatei[12], qstatei[13], qstatei[14], qstatei[15], qstatei[16], qstatei[17], qstatei[18], qstatei[19], qstatei[20], qstatei[21], qstatei[22], qstatei[23], qstatei[24], qstatei[25], qstatei[26], qstatei[27], qstatei[28], qstatei[29], qstatei[30], qstatei[31]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        boolean $$_tmp_measureVar26;
        if (q_state_0[16] * q_state_0[16] + q_state_1[16] * q_state_1[16] + q_state_0[17] * q_state_0[17] + q_state_1[17] * q_state_1[17] + q_state_0[18] * q_state_0[18] + q_state_1[18] * q_state_1[18] + q_state_0[19] * q_state_0[19] + q_state_1[19] * q_state_1[19] + q_state_0[20] * q_state_0[20] + q_state_1[20] * q_state_1[20] + q_state_0[21] * q_state_0[21] + q_state_1[21] * q_state_1[21] + q_state_0[22] * q_state_0[22] + q_state_1[22] * q_state_1[22] + q_state_0[23] * q_state_0[23] + q_state_1[23] * q_state_1[23] + q_state_0[24] * q_state_0[24] + q_state_1[24] * q_state_1[24] + q_state_0[25] * q_state_0[25] + q_state_1[25] * q_state_1[25] + q_state_0[26] * q_state_0[26] + q_state_1[26] * q_state_1[26] + q_state_0[27] * q_state_0[27] + q_state_1[27] * q_state_1[27] + q_state_0[28] * q_state_0[28] + q_state_1[28] * q_state_1[28] + q_state_0[29] * q_state_0[29] + q_state_1[29] * q_state_1[29] + q_state_0[30] * q_state_0[30] + q_state_1[30] * q_state_1[30] + q_state_0[31] * q_state_0[31] + q_state_1[31] * q_state_1[31] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3] + q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] + q_state_0[8] * q_state_0[8] + q_state_1[8] * q_state_1[8] + q_state_0[9] * q_state_0[9] + q_state_1[9] * q_state_1[9] + q_state_0[10] * q_state_0[10] + q_state_1[10] * q_state_1[10] + q_state_0[11] * q_state_0[11] + q_state_1[11] * q_state_1[11] + q_state_0[12] * q_state_0[12] + q_state_1[12] * q_state_1[12] + q_state_0[13] * q_state_0[13] + q_state_1[13] * q_state_1[13] + q_state_0[14] * q_state_0[14] + q_state_1[14] * q_state_1[14] + q_state_0[15] * q_state_0[15] + q_state_1[15] * q_state_1[15]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31]};
            $$_tmp_measureVar26 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar26 = false;
        }
        boolean b_0 = $$_tmp_measureVar26;
        assert b_0 == b_test;
    }
    /*@
      requires qstate != null && qstatei != null && qstate.length == 32 && qstatei.length == 32;
      requires (\exists int i; i >= 0 && i < qstate.length; qstate[i] == 1.0F && (\forall int j; j >= 0 && j < qstate.length; (i != j) ==> qstate[j] == 0.0F));
      requires (\forall int i; i >= 0 && i < qstate.length; qstatei[i] == 0.0F);
   */

    public static void gatesTest_5_9(/*@ non_null */
            float[] qstate, /*@ non_null */
            float[] qstatei) {
        boolean b_test = false;
        for (int i = 16; i < qstate.length; ++i) {
            b_test = b_test || qstate[i] == 1.0F;
        }
        float[] q_state_0 = new float[]{qstate[0], qstate[1], qstate[2], qstate[3], qstate[4], qstate[5], qstate[6], qstate[7], qstate[8], qstate[9], qstate[10], qstate[11], qstate[12], qstate[13], qstate[14], qstate[15], qstate[16], qstate[17], qstate[18], qstate[19], qstate[20], qstate[21], qstate[22], qstate[23], qstate[24], qstate[25], qstate[26], qstate[27], qstate[28], qstate[29], qstate[30], qstate[31]};
        float[] q_state_1 = new float[]{qstatei[0], qstatei[1], qstatei[2], qstatei[3], qstatei[4], qstatei[5], qstatei[6], qstatei[7], qstatei[8], qstatei[9], qstatei[10], qstatei[11], qstatei[12], qstatei[13], qstatei[14], qstatei[15], qstatei[16], qstatei[17], qstatei[18], qstatei[19], qstatei[20], qstatei[21], qstatei[22], qstatei[23], qstatei[24], qstatei[25], qstatei[26], qstatei[27], qstatei[28], qstatei[29], qstatei[30], qstatei[31]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        q_state_0 = new float[]{q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31], q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15]};
        q_state_1 = new float[]{q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31], q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15]};
        boolean $$_tmp_measureVar27;
        if (q_state_0[16] * q_state_0[16] + q_state_1[16] * q_state_1[16] + q_state_0[17] * q_state_0[17] + q_state_1[17] * q_state_1[17] + q_state_0[18] * q_state_0[18] + q_state_1[18] * q_state_1[18] + q_state_0[19] * q_state_0[19] + q_state_1[19] * q_state_1[19] + q_state_0[20] * q_state_0[20] + q_state_1[20] * q_state_1[20] + q_state_0[21] * q_state_0[21] + q_state_1[21] * q_state_1[21] + q_state_0[22] * q_state_0[22] + q_state_1[22] * q_state_1[22] + q_state_0[23] * q_state_0[23] + q_state_1[23] * q_state_1[23] + q_state_0[24] * q_state_0[24] + q_state_1[24] * q_state_1[24] + q_state_0[25] * q_state_0[25] + q_state_1[25] * q_state_1[25] + q_state_0[26] * q_state_0[26] + q_state_1[26] * q_state_1[26] + q_state_0[27] * q_state_0[27] + q_state_1[27] * q_state_1[27] + q_state_0[28] * q_state_0[28] + q_state_1[28] * q_state_1[28] + q_state_0[29] * q_state_0[29] + q_state_1[29] * q_state_1[29] + q_state_0[30] * q_state_0[30] + q_state_1[30] * q_state_1[30] + q_state_0[31] * q_state_0[31] + q_state_1[31] * q_state_1[31] > q_state_0[0] * q_state_0[0] + q_state_1[0] * q_state_1[0] + q_state_0[1] * q_state_0[1] + q_state_1[1] * q_state_1[1] + q_state_0[2] * q_state_0[2] + q_state_1[2] * q_state_1[2] + q_state_0[3] * q_state_0[3] + q_state_1[3] * q_state_1[3] + q_state_0[4] * q_state_0[4] + q_state_1[4] * q_state_1[4] + q_state_0[5] * q_state_0[5] + q_state_1[5] * q_state_1[5] + q_state_0[6] * q_state_0[6] + q_state_1[6] * q_state_1[6] + q_state_0[7] * q_state_0[7] + q_state_1[7] * q_state_1[7] + q_state_0[8] * q_state_0[8] + q_state_1[8] * q_state_1[8] + q_state_0[9] * q_state_0[9] + q_state_1[9] * q_state_1[9] + q_state_0[10] * q_state_0[10] + q_state_1[10] * q_state_1[10] + q_state_0[11] * q_state_0[11] + q_state_1[11] * q_state_1[11] + q_state_0[12] * q_state_0[12] + q_state_1[12] * q_state_1[12] + q_state_0[13] * q_state_0[13] + q_state_1[13] * q_state_1[13] + q_state_0[14] * q_state_0[14] + q_state_1[14] * q_state_1[14] + q_state_0[15] * q_state_0[15] + q_state_1[15] * q_state_1[15]) {
            q_state_0 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_0[16], q_state_0[17], q_state_0[18], q_state_0[19], q_state_0[20], q_state_0[21], q_state_0[22], q_state_0[23], q_state_0[24], q_state_0[25], q_state_0[26], q_state_0[27], q_state_0[28], q_state_0[29], q_state_0[30], q_state_0[31]};
            q_state_1 = new float[]{0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, q_state_1[16], q_state_1[17], q_state_1[18], q_state_1[19], q_state_1[20], q_state_1[21], q_state_1[22], q_state_1[23], q_state_1[24], q_state_1[25], q_state_1[26], q_state_1[27], q_state_1[28], q_state_1[29], q_state_1[30], q_state_1[31]};
            $$_tmp_measureVar27 = true;
        } else {
            q_state_0 = new float[]{q_state_0[0], q_state_0[1], q_state_0[2], q_state_0[3], q_state_0[4], q_state_0[5], q_state_0[6], q_state_0[7], q_state_0[8], q_state_0[9], q_state_0[10], q_state_0[11], q_state_0[12], q_state_0[13], q_state_0[14], q_state_0[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            q_state_1 = new float[]{q_state_1[0], q_state_1[1], q_state_1[2], q_state_1[3], q_state_1[4], q_state_1[5], q_state_1[6], q_state_1[7], q_state_1[8], q_state_1[9], q_state_1[10], q_state_1[11], q_state_1[12], q_state_1[13], q_state_1[14], q_state_1[15], 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F, 0.0F};
            $$_tmp_measureVar27 = false;
        }
        boolean b_0 = $$_tmp_measureVar27;
        assert b_0 != b_test;
    }
}
