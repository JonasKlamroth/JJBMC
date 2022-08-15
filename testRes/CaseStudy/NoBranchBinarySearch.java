class NoBranchBinarySearch {

    public static final int K = 5;

    /*@ public static invariant K==5;*/



    /*@ normal_behaviour
      @   requires a != null;
      @   requires (1 << K) - 1 == a.length;
      @   requires (\forall int x; 0 <= x < a.length - 1; a[x] < a[x+1]);
      @   ensures 0 <= \result <= a.length;
      @   ensures \result < a.length ==> v <= a[\result];
      @   ensures \result > 0 ==> v > a[\result-1];
      @   assignable \nothing;
      @*/
    static int search(int[] a, int v) {
        int b = a.length;
        for(int d = 1 << K; d > 1;) {
            d >>= 1;
            b = a[b-d] < v ? b : b - d;
        }
        return b - 1;
    }
}