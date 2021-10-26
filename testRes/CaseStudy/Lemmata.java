class Lemmata {

    /*@ normal_behaviour
      @  requires 0.0 <= f < 1000000.0;
      @  ensures (double)(int)f <= f < ((double)(int)f) + 1.0;
      @  assignable \nothing;
      @*/
    static void lemma(float f) {
    }

    public static /*@ pure */ int countEven(/*@nullable*/Object[] a) {
        int result = 0;
        for(int i = 0; i < a.length; i += 2) {
            if(a[i] != null) {
                result ++;
            }
        }
        return result;
    }

    /*@ public normal_behaviour
      @  requires a != null;
      @  requires a.length % 2 == 0;
      @  requires a.length <= 20;
      @  requires countEven(a) < a.length / 2 - 1;
      @  requires a.length >= 8;
      @  ensures (\exists int nul1; 0 <= nul1 < a.length/2;
      @             \exists int nul2; nul1 < nul2 && nul2 < a.length/2;
      @     a[2 * nul1] == null && a[2 * nul2] == null);
      @  assignable \nothing;
      @*/
    public static int lemmaTwoNulls(/*@nullable*/ Object[] a) {
        return 0;
    }
}