public class BubbleSortBroken {
    /*@
      @ requires arr != null && arr.length <= 5;
      @ ensures (\forall int v; 0 <= v && v <= \result.length - 1; (\forall int w; 0 <= w && w <= v - 1; \result[w] < \result[v]));
      @ assignable arr[*];
      @*/
    static int[] sort(int arr[]) {
        //@ loop_invariant j <= arr.length - 1 && -1 <= j;
        //@ loop_invariant (\forall int k; j < k && k < arr.length; (\forall int k1; 0 <= k1 && k1 < k; arr[k1] <= arr[k]));
        //@ loop_modifies arr[*];
        for (int j = arr.length - 1; j >= 0; --j) {
            //Inv2: max(arr, 0, j) == max(arr, i, j)
            //@ loop_invariant 0 <= i && i <= j;
            //@ loop_invariant (\forall int m; 0 <= m && m < i; arr[m] <= arr[i]);
            //@ loop_invariant (\forall int k; j < k && k < arr.length; (\forall int k1; 0 <= k1 && k1 < k; arr[k1] <= arr[k]));
            //@ loop_modifies arr[0 .. j - 1];
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
    static void swap(int array[], int first, int second) {
        array[first] = array[first] ^ array[second];
        array[second] = array[second] ^ array[first];
        array[first] = array[first] ^ array[second];
    }
}
