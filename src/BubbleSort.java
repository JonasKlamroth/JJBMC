/**
 * Created by jklamroth on 10/26/18.
 */
class BubbleSort {
    /*@
      @ requires arr != null;
      @ ensures (\forall int i; i >= 0 && i <= arr.length - 1; (\forall int j; j >= 0 && j <= i - 1; arr[i] > arr[j]));
      @ assignable arr[*];
      @*/
    static int[] sort(int arr[]) {
        boolean sorted = false;
        while(!sorted) {
            sorted = true;
            for(int i = 0; i < arr.length - 1; ++i) {
                if(arr[i] > arr[i + 1]) {
                    swap(arr, i, i+1);
                    sorted = false;
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
