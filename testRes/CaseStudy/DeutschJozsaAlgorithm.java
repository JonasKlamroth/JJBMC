import java.io.*;
import java.util.*;

public class DeutschJozsaAlgorithm {
    public static void main(String[] args) {
        Function f = new Function() {
            @java.lang.Override
            public boolean exec(boolean input) {
                return false;
            }
        };
        System.out.println(DeutschAlgorithm.isBalancedGenerated(DeutschAlgorithm.fToArray(f)));
    }

    public static boolean[] fToArray(Function f) {
        return new boolean[]{f.exec(false), f.exec(true)};
    }

    //@ requires f != null && f.length & (f.length - 1) == 0;
    //@ ensures \result <==> (f[0] != f[1]);
    public static boolean isBalanced(boolean f[]) {
        boolean cBit = true;
        double h = 0.70710678118;
        double[] q1 = new double[]{0.0, 1.0};
        double[] q2 = new double[]{h, -h};

        q1 = new double[]{1*h + 0*h, 1*h + 0*(-h)};

        double[] c = new double[]{q1[0]*q2[0], q1[0]*q2[1], q1[1]*q2[0], q1[1]*q2[1]};

        double [][] m = getOperatorForFunction(f);

        c = new double[]{
                m[0][0]*c[0] + m[0][1]*c[1] + m[0][2]*c[2] + m[0][3]*c[3],
                m[1][0]*c[0] + m[1][1]*c[1] + m[1][2]*c[2] + m[1][3]*c[3],
                m[2][0]*c[0] + m[2][1]*c[1] + m[2][2]*c[2] + m[2][3]*c[3],
                m[3][0]*c[0] + m[3][1]*c[1] + m[3][2]*c[2] + m[3][3]*c[3]
        };

        double[][] hm = new double[][]{
                new double[]{h, 0.f, h, 0.f},
                new double[]{0.f, h, 0.f, h},
                new double[]{h, 0.f, -h, 0.f},
                new double[]{0.f, h, 0.f, -h}
        };

        c = new double[] {
                hm[0][0]*c[0] + hm[0][1]*c[1] + hm[0][2]*c[2] + hm[0][3]*c[3],
                hm[1][0]*c[0] + hm[1][1]*c[1] + hm[1][2]*c[2] + hm[1][3]*c[3],
                hm[2][0]*c[0] + hm[2][1]*c[1] + hm[2][2]*c[2] + hm[2][3]*c[3],
                hm[3][0]*c[0] + hm[3][1]*c[1] + hm[3][2]*c[2] + hm[3][3]*c[3]
        };

        double sum0 = c[0]*c[0] + c[1] * c[1];
        double sum1 = c[2]*c[2] + c[3] * c[3];
        if(sum0 > sum1) {
            cBit = false;
            if(sum0 == 0) {
                assert false;
            }
            c = new double[]{
                    c[0],
                    c[1],
                    0.0,
                    0.0
            };
            System.out.println(Arrays.toString(c));
            return cBit;
        } else {
            cBit = true;
            if(sum1 == 0) {
                assert false;
            }
            c = new double[]{
                    0.0,
                    0.0,
                    c[2],
                    c[3]
            };
            System.out.println(Arrays.toString(c));
            return cBit;
        }
    }

    //@ requires f != null && f.length == 2;
    //@ ensures \result <==> (f[0] != f[1]);
    static boolean isBalancedGenerated(boolean[] f) {
        float[] q_res = null;
        boolean[] c_res = null;
        float[] q_1 = new float[]{1.0f,0.0f,0.0f,0.0f,};
        float[] q_2 = new float[]{(q_1[1]),(q_1[0]),(q_1[3]),(q_1[2]),};
        float[] q_3 = new float[]{(0.70710677f * (q_2[0]) + 0.70710677f * (q_2[1])),(0.70710677f * (q_2[0]) + -0.70710677f * (q_2[1])),(0.70710677f * (q_2[2]) + 0.70710677f * (q_2[3])),(0.70710677f * (q_2[2]) + -0.70710677f * (q_2[3])),};
        System.out.println(Arrays.toString(q_3));
        float[] q_4 = new float[]{(0.70710677f * (q_3[0]) + 0.70710677f * (q_3[2])),(0.70710677f * (q_3[1]) + 0.70710677f * (q_3[3])),(0.70710677f * (q_3[0]) + -0.70710677f * (q_3[2])),(0.70710677f * (q_3[1]) + -0.70710677f * (q_3[3])),};
        float[] q_5 = new float[]{((!f[0] ? 1.0f : 0.0f) * (q_4[0]) + (f[0] ? 1.0f :0.0f) * (q_4[1])),((f[0] ? 1.0f : 0.0f) * (q_4[0]) + (!f[0] ? 1.0f :0.0f) * (q_4[1])),((!f[1] ? 1.0f : 0.0f) * (q_4[2]) + (f[1] ? 1.0f :0.0f) * (q_4[3])),((f[1] ? 1.0f : 0.0f) * (q_4[2]) + (!f[1] ? 1.0f :0.0f) * (q_4[3])),};
        float[] q_6 = new float[]{(0.70710677f * (q_5[0]) + 0.70710677f * (q_5[2])),(0.70710677f * (q_5[1]) + 0.70710677f * (q_5[3])),(0.70710677f * (q_5[0]) + -0.70710677f * (q_5[2])),(0.70710677f * (q_5[1]) + -0.70710677f * (q_5[3])),};
        float dvar_1 = (q_6[0] * q_6[0]) + (q_6[1] * q_6[1]) + 0.0f;
        float dvar_2 = (q_6[2] * q_6[2]) + (q_6[3] * q_6[3]) + 0.0f;
        if(dvar_1 < dvar_2) {
            float[] q_7 = new float[]{0.0f,0.0f,(q_6[2]),(q_6[3]),};
            boolean[] c_1 = new boolean[]{false};
            q_res = q_7;
            c_res = c_1;
        } else {
            float[] q_8 = new float[]{(q_6[0]),(q_6[1]),0.0f,0.0f,};
            boolean[] c_2 = new boolean[]{true};
            q_res = q_8;
            c_res = c_2;
        }
        return !c_res[0];
    }

    static double sqrt(double m)
    {
        double i=0;
        double x1,x2;
        x2 = 0;
        while( (i*i) <= m )
            i+=0.2f;
        x1=i;
        for(int j=0;j<5;j++)
        {
            x2=m;
            x2/=x1;
            x2+=x1;
            x2/=2;
            x1=x2;
        }
        return x2;
    }

    //@ requires f != null && f.length == 2;
    //@ assignable \nothing;
    private static double[][] getOperatorForFunction(boolean f[]) {
        return new double[][] {
                new double[]{boolToDouble(!f[0]), boolToDouble(f[0]), 0.f, 0.f},
                new double[]{boolToDouble(f[0]), boolToDouble(!f[0]), 0.f, 0.f},
                new double[]{0.f, 0.f, boolToDouble(!f[1]), boolToDouble(f[1])},
                new double[]{0.f, 0.f, boolToDouble(f[1]), boolToDouble(!f[1])}
        };
    }

    private static double boolToDouble(boolean b) {
        return b ? 1.0 : 0.0;
    }

    static abstract class Function {
        public /*@ pure */ abstract boolean exec(boolean input);
    }
}