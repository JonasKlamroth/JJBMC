public class BaseSort {

    public static final int THRESHOLD = 6;

    /*+KeY@ public normal_behaviour
      @ ensures \result == (\num_of int j; 0<=j<a.length; a[j] == el);
      @ assignable \strictly_nothing;
      @*/
    public static /*@ pure */ int count(int[] a, int el) {
        int sum = 0;
        /*+KeY@
          @ loop_invariant 0 <= i && i <= a.length;
          @ loop_invariant sum == (\num_of int j; 0<=j<i; a[j] == el);
          @ assignable \strictly_nothing;
          @ decreases a.length - i;
          @*/
        for (int i = 0; i < a.length; ++i) {
            if (a[i] == el) {
                sum++;
            }
        }
        return sum;
    }

    /*+OPENJML@ public normal_behaviour
      @  requires a != null;
      @  requires to - fr < THRESHOLD;
      @  requires 0 <= fr && fr < to && to < a.length;
      @  requires fr > 0 ==> (\forall int x; fr<=x && x<=to; a[x] > a[fr-1]);
      @  requires to < a.length-1 ==> (\forall int x; fr<=x && x<=to; a[x] <= a[to+1]);
      @  ensures (\forall int i; fr<=i && i<to; a[i] <= a[i+1]);
      @  ensures (\forall int i; 0 <= i && i < a.length;
      @      count(a, \old(a[i])) == \old(count(a, a[i])));
      @  ensures fr > 0 ==> (\forall int x; fr<=x && x<=to; a[x] > a[fr-1]);
      @  ensures to < a.length-1 ==> (\forall int x; fr<=x && x<=to; a[x] <= a[to+1]);
      @  assignable a[fr .. to];
      @*/
    /*+KeY@ public normal_behaviour
      @  requires a != null;
      @  requires to - fr < THRESHOLD;
      @  requires 0 <= fr && fr < to && to <= a.length;
      @  requires fr > 0 ==> (\forall int x; fr<=x && x<=to; a[x] > a[fr-1]);
      @  requires to < a.length-1 ==> (\forall int x; fr<=x && x<=to; a[x] <= a[to+1]);
      @  ensures (\forall int i; fr<=i && i<to; a[i] <= a[i+1]);
      @  ensures \dl_seqPerm(\dl_array2seq(a), \old(\dl_array2seq(a)));
      @  ensures fr > 0 ==> (\forall int x; fr<=x && x<=to; a[x] > a[fr-1]);
      @  ensures to < a.length-1 ==> (\forall int x; fr<=x && x<=to; a[x] <= a[to+1]);
      @  assignable a[fr .. to];
      @*/
    public static void baseSort(int[] a, int fr, int to) {
        if (fr + 2 <= to)
            swap(a, fr + 1, fr + 2);
        if (fr + 2 <= to)
            swap(a, fr + 0, fr + 2);
        if (fr + 1 <= to)
            swap(a, fr + 0, fr + 1);
        if (fr + 5 <= to)
            swap(a, fr + 4, fr + 5);
        if (fr + 5 <= to)
            swap(a, fr + 3, fr + 5);
        if (fr + 4 <= to)
            swap(a, fr + 3, fr + 4);
        if (fr + 3 <= to)
            swap(a, fr + 0, fr + 3);
        if (fr + 4 <= to)
            swap(a, fr + 1, fr + 4);
        if (fr + 5 <= to)
            swap(a, fr + 2, fr + 5);
        if (fr + 4 <= to)
            swap(a, fr + 2, fr + 4);
        if (fr + 3 <= to)
            swap(a, fr + 1, fr + 3);
        if (fr + 3 <= to)
            swap(a, fr + 2, fr + 3);
    }

    /*@ private behaviour
      @  requires array != null;
      @  requires pos < pos1 && pos >= 0 && pos1 < array.length;
      @  ensures array[pos] <= array[pos1];
      @  ensures (array[pos] == \old(array[pos]) && array[pos1] == \old(array[pos1])) ||
      @          (array[pos1] == \old(array[pos]) && array[pos] == \old(array[pos1]));
      @  assignable array[pos], array[pos1];
      @*/
    private static void swap(int[] array, int pos, int pos1) {
        if (pos >= 0 && pos1 >= 0 && pos < array.length && pos1 < array.length && array[pos] > array[pos1]) {
            array[pos] ^= array[pos1];
            array[pos1] ^= array[pos];
            array[pos] ^= array[pos1];
        }
    }



    /*@ requires arr != null && arr1 != null && arr.length == arr1.length;
      @ requires Utils.isNonNegative(arr);
      @ requires (\forall int i; 0 <= i && i < arr.length; count(arr, arr[i]) == count(arr1, arr[i]));
      @ ensures Utils.isNonNegative(arr1);
      @*/
    private static final void lemmaPerm(int[] arr, int[] arr1) {
    }
}