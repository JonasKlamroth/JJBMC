package CaseStudy;

import TestAnnotations.Unwind;
import TestAnnotations.Verifyable;

/**
 * Created by jklamroth on 10/26/18.
 */
class BubbleSort {
    /*@
      @ requires arr != null && arr.length <= 5;
      @ ensures (\forall int v; 0 <= v && v <= \result.length - 1; (\forall int w; 0 <= w && w <= v - 1; \result[w] <= \result[v]));
      @ assignable arr[*];
      @*/
    @Verifyable
    @Unwind(number = 7)
    static int[] sort(int arr[]) {
        for (int j = arr.length - 1; j >= 0; --j) {
            for (int i = 0; i < j; ++i) {
                if (arr[i] > arr[i + 1]) {
                    swap(arr, i, i + 1);
                }
            }
        }
        return arr;
    }

    /*@
      @ requires array != null && 2 <= array.length;
      @ requires first < array.length && 0 <= first;
      @ requires second < array.length && 0 <= second;
      @ requires first != second;
      @ ensures \old(array[first]) == array[second] && \old(array[second]) == array[first];
      @ assignable array[first], array[second];
      @*/
    @Verifyable
    static void swap(int array[], int first, int second) {
        array[first] = array[first] ^ array[second];
        array[second] = array[second] ^ array[first];
        array[first] = array[first] ^ array[second];
    }
}
