public class DeutschAlgorithm {
    public static void main(String[] args) {
        Function f = new Function() {
            @java.lang.Override
            public boolean exec(boolean input) {
                return input;
            }
        };
        System.out.println(DeutschAlgorithm.isBalanced(DeutschAlgorithm.fToArray(f)));
    }

    public static boolean[] fToArray(Function f) {
        return new boolean[]{f.exec(false), f.exec(true)};
    }

    //@ requires f != null && f.length == 2;
    //@ ensures \result <==> (f[0] != f[1]);
    public static boolean isBalanced(boolean f[]) {
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

        System.out.println(c[0]*c[0] + c[1]*c[1]);
        System.out.println(c[2]*c[2] + c[3]*c[3]);
        return c[0]*c[0] + c[1]*c[1]  + 2.0 < c[2]*c[2] + c[3]*c[3];
    }

    //@ requires f != null && f.length == 2;
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