public class NanoInsertionSort {

    /*@
      @ normal_behaviour
      @ requires a != null && a.length < 5;
      @ requires low >= 1 && low < high && high <= a.length;
      @ requires (\forall int j; low <= j < high; (\exists int i; 0 <= i < low; a[i] <= a[j]));
      @ ensures (\forall int i; low <= i && i < high - 1; a[i] <= a[i+1]);
      @ assignable a[*];
      @*/
    static void nanoInsertionSort(int[] a, int low, int high) {
        for (int k; ++low < high; ) {
            k = low;
            int ak = a[k];

            while (ak < a[--k]) {
                a[k + 1] = a[k];
            }
            a[k + 1] = ak;
        }
   }
}