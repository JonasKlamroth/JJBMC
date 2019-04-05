
/**
 * This class implements sorting algorithms by Vladimir Yaroslavskiy,
 * such as Merging sort, the pair, nano and optimized insertion sorts,
 * counting sort and heap sort, invoked from the Dual-Pivot Quicksort.
 *
 * @author Vladimir Yaroslavskiy
 * @version 2018.02.18
 * @since 10
 */
final class SortingAlgorithms {

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
      @ ensures (\forall int i; low <= i && i < high-2; a[i] <= a[i+1]);
      @ assignable a[*];
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