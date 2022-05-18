import java.util.Arrays;
/**
 * This class implements sorting algorithms by Vladimir Yaroslavskiy,
 * such as Merging sort, the pair, nano and optimized insertion sorts,
 * counting sort and heap sort, invoked from the Dual-Pivot Quicksort.
 *
 * @author Vladimir Yaroslavskiy
 * @version 2018.02.18
 * @since 10
 */
public class NanoInsertionSort {

    /**
     * Sorts the specified range of the array by the nano insertion sort.
     *
     * @param a    the array to be sorted
     * @param low  the index of the first element, inclusive, to be sorted
     * @param high the index of the last element, exclusive, to be sorted
     */
    /*@
      @ normal_behaviour
      @ requires a != null && a.length <=5;
      @ requires low >= 1 && low < high && high <= a.length;
      @ requires (\forall int j; low <= j < high; (\exists int i; 0 <= i < low; a[i] <= a[j]));
      @ ensures (\forall int i; low <= i && i < high - 1; a[i] <= a[i+1]);
      @ assignable a[low .. high - 1];
      @*/
    static void nanoInsertionSort(int[] a, int low, int high) {
        /*
         * In the context of Quicksort, the elements from the left part
         * play the role of sentinels. Therefore expensive check of the
         * left range on each iteration can be skipped.
         */
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