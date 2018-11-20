/**
 * Created by jklamroth on 10/26/18.
 */
class BubbleSort {
    /*@
      @ requires arr != null;
      @ ensures (\forall int v; v >= 0 && v <= \result.length - 1; (\forall int w; w >= 0 && w <= v - 1; \result[v] > \result[w]));
      @ assignable arr[*];
      @*/
    static int[] sort(int arr[]) {
        //@ loop_invariant (\forall int k; k > j && k < arr.length - 1; arr[k] <= arr[k + 1]);
        //@ loop_modifies arr[*];
        for(int j = arr.length - 1; j >= 0; --j) {
            //Inv2: max(arr, 0, j) == max(arr, i, j)
            //@ loop_invariant (\forall int m; m >= 0 && m < i; arr[i] >= arr[m]);
            //@ loop_modifies arr[i], arr[i + 1];
            for (int i = 0; i < j; ++i) {
                if (arr[i] > arr[i + 1]) {
                    swap(arr, i, i + 1);
                }
            }
        }
        return arr;
    }

    /*@
      @ requires array != null && array.length >= 2;
      @ requires first < array.length && first >= 0;
      @ requires second < array.length && second >= 0;
      @ requires first != second;
      @ ensures \old(array)[first] == array[second] && \old(array)[second] == array[first];
      @ assignable array[first], array[second];
      @*/
    static void swap(int array[], int first, int second) {
        array[first] = array[first] ^ array[second];
        array[second] = array[second] ^ array[first];
        array[first] = array[first] ^ array[second];
    }
}
