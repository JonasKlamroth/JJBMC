package CaseStudy;

import TestAnnotations.Unwind;
import TestAnnotations.Verifyable;

/**
 * Created by jklamroth on 10/26/18.
 */
class BubbleSortSymb {
    /*@
      @ requires arr != null;
      @ ensures (\forall int v; v >= 0 && v <= \result.length - 1; (\forall int w; w >= 0 && w <= v - 1; \result[v] >= \result[w]));
      @ ensures false;
      @ assignable arr[*];
      @*/
    @Verifyable
    @Unwind(number = 10)
    static int[] sort(int arr[]) {
        //@ loop_invariant j <= arr.length - 1 && j >= -1;
        //@ loop_invariant (\forall int k; k > j && k < arr.length; (\forall int k1; k1 >= 0 && k1 < k; arr[k1] <= arr[k]));
        //@ loop_modifies arr[*];
        for(int j = arr.length - 1; j >= 0; --j) {
            //Inv2: max(arr, 0, j) == max(arr, i, j)
            //@ loop_invariant i >= 0 && i <= j;
            //@ loop_invariant (\forall int m; m >= 0 && m < i; arr[i] >= arr[m]);
            //@ loop_invariant (\forall int k; k > j && k < arr.length; (\forall int k1; k1 >= 0 && k1 < k; arr[k1] <= arr[k]));
            //@ loop_modifies arr[0 .. j - 1];
            for (int i = 0; i < j; ++i) {
                if (arr[i] > arr[i + 1]) {
                    swap(arr, i, i + 1);
                }
            }
        }
        return arr;
    }

    static void swap(int array[], int first, int second) {
        array[first] = array[first] ^ array[second];
        array[second] = array[second] ^ array[first];
        array[first] = array[first] ^ array[second];
    }
}
