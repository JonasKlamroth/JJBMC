class Specs {

    /*+KEY@ public normal_behaviour
      @  requires a != null;
      @  requires a.length % 2 == 0;
      @  ensures \result == (\num_of \bigint i;
      @       0 <= i < a.length / (\bigint)2;
      @       a[2 * i] != null);
      @  assignable \strictly_nothing;
      @*/
    public static /*@ pure */ int countEven(/*@nullable*/Object[] a) {
        int result = 0;

        /*+KEY@ loop_invariant
          @  result == (\num_of \bigint j;
          @       0 <= j < i/2;
          @       a[2 * j] != null);
          @ loop_invariant 0 <= i <= a.length;
          @ loop_invariant i%2 == 0;
          @ decreases a.length + 1 - i;
          @ assignable \strictly_nothing;
          @*/
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
      @  requires countEven(a) < a.length / 3;
      @  requires a.length >= 8;
      @  ensures (\exists int nul1; 0 <= nul1 < a.length/2;
      @             \exists int nul2; nul1 < nul2 && nul2 < a.length/2;
      @     a[2 * nul1] == null && a[2 * nul2] == null);
      @  assignable \nothing;
      @*/
    public static int lemmaTwoNulls(/*@nullable*/ Object[] a) {
        //lemmaSumOfNums(a);
        return 0;
    }

    /*+KEY@ normal_behaviour
      @  requires a != null;
      @  requires a.length % 2 == 0;
      @  ensures (\num_of \bigint i; 0 <= i < a.length / (\bigint)2; a[2*i] != null) +
      @    (\num_of \bigint i; 0 <= i < a.length / (\bigint)2; a[2*i] == null) == a.length/2;
      @  assignable \strictly_nothing;
      @*/
    private static void lemmaSumOfNums(/*@nullable*/ Object[] a) {

        /*+KEY@ loop_invariant 0<=k<=a.length/2;
          @ loop_invariant (\num_of \bigint i; 0 <= i < k; a[2*i] != null) +
          @    (\num_of \bigint i; 0 <= i < k; a[2*i] == null) == k;
          @ decreases a.length/2 - k;
          @ assignable \strictly_nothing;
          @*/
        for(int k=0; k < a.length/2; k++) {
        }
    }


    /*@ normal_behaviour
      @  requires true; // ... specs missing
      @  ensures true;
      @*/
    void useCase(/*@nullable*/ Object[] a) {
        // ghost int lemma;
        // somewhere in the code, we can invoke the lemma

        // set lemma = lemmaTwoNulls(a);
        ;

        // then the rest of the code again
    }
}