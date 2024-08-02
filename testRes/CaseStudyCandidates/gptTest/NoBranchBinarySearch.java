class NoBranchBinarySearch {

    public static final int K = 3;



    /*@ public static invariant K == 3; */



    /*@

        normal_behaviour

        requires a != null;

        requires (1 << K) - 1 == a.length;

        requires (\forall int x; 0 <= x < a.length - 1; a[x] < a[x + 1]);

        ensures 0 <= \result <= a.length;

        ensures \result < a.length ==> v <= a[\result];

        ensures \result > 0 ==> v > a[\result - 1];

    @*/

    static int search(int[] a, int v) {

        int b = a.length;



        /*@

            @ maintaining 1 < d && d <= (1 << K);

            @ maintaining 0 <= b && b <= a.length;

            @ maintaining (\forall int i; 0 <= i && i < b; a[i] < v);

            @ maintaining (\forall int i; b < i && i < a.length; a[i] >= v);

            @ decreases d * a.length;

        @*/

        for (int d = 1 << (K - 1); d > 0; d >>= 1) {

            //@ assert 0 <= b - d && b - d < a.length;

            //@ assert 0 <= b && b <= a.length;

            if (v > a[b - d]) {

                b -= d;

            }

        }



        //@ assert (b == a.length || v <= a[b]);

        //@ assert (b == 0 || v > a[b - 1]);



        return b;

    }

}