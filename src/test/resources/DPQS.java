/* trying to prove the adapted dpq of 2018.
   removed all non-int[] methods and all hints to parallel algorithms
 */

/**
 * This class implements powerful and fully optimized versions, both
 * sequential and parallel, of the Dual-Pivot Quicksort algorithm by
 * Vladimir Yaroslavskiy, Jon Bentley and Josh Bloch. This algorithm
 * offers O(n log(n)) performance on all data sets, and is typically
 * faster than traditional (one-pivot) Quicksort implementations.
 *
 * @author Vladimir Yaroslavskiy
 * @author Jon Bentley
 * @author Josh Bloch
 *
 * @version 2018.02.18
 * @since 1.7
 */
final class DPQS {

    private static void srt(int[] a, int bits, int low, int high) {
        int end = high - 1, length = high - low;


        /*
         * The splitting of the array, defined by the following
         * step, is related to the inexpensive approximation of
         * the golden ratio.
         * js: replaced ">> 3" by "/8"
         */
        int step = (length / 8) * 3 + 3;

        /*
         * Five elements around (and including) the central element in
         * the array will be used for pivot selection as described below.
         * The unequal choice of spacing these elements was empirically
         * determined to work well on a wide variety of inputs.
         * * js: replaced ">>> 1" by "/ 2"
         */
        int e1 = low + step;
        int e5 = end - step;
        int e3 = (e1 + e5) / 2;
        int e2 = (e1 + e3) / 2;
        int e4 = (e3 + e5) / 2;

        /*
         * Sort these elements in place by the combination
         * of 5-element sorting network and insertion sort.
         */
        /*@
          @ requires a != null && a.length <= 30;
          @ requires 0 <= low && high <= a.length;
          @ requires low <= e1 && e1 < e2 && e2 < e3 && e3 < e4 && e4 < e5 && e5 < high;
          @ ensures a[e1] <= a[e2] && a[e2] <= a[e3] && a[e3] <= a[e4] && a[e4] <= a[e5];
          @ assignable a[e1], a[e2], a[e3], a[e4], a[e5];
          @*/
        {
            {if (a[e5] < a[e3]) { int t = a[e5]; a[e5] = a[e3]; a[e3] = t; }}

            {if (a[e4] < a[e2]) { int t = a[e4]; a[e4] = a[e2]; a[e2] = t; }}

            {if (a[e5] < a[e4]) { int t = a[e5]; a[e5] = a[e4]; a[e4] = t; }}

            {if (a[e3] < a[e2]) { int t = a[e3]; a[e3] = a[e2]; a[e2] = t; }}

            {if (a[e4] < a[e3]) { int t = a[e4]; a[e4] = a[e3]; a[e3] = t; }}

            {if (a[e1] > a[e2]) { int t = a[e1]; a[e1] = a[e2]; a[e2] = t;
                if (t > a[e3]) { a[e2] = a[e3]; a[e3] = t;
                    if (t > a[e4]) { a[e3] = a[e4]; a[e4] = t;
                        if (t > a[e5]) { a[e4] = a[e5]; a[e5] = t; }
                    }
                }
            }
            }
        }
    }
}
