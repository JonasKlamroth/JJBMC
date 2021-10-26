import java.util.Arrays;
public class BitSort {
    private static void sort(int[] array, int i, int from, int to) {
        if(i < 0 || to - from <= 1) {
            return;
        }

        int mask = 1 << i;
        int swapPos = from;
        for(int j = from; j < to; ++j) {
            if((array[j] & mask) == 0 ) {
                swap(array, j, swapPos++);
            }
        }
        BitSort.sort(array, i - 1, from, swapPos);
        BitSort.sort(array, i - 1, swapPos, to);
    }

    private static void sort(int[] array) {
        BitSort.sort(array, 30, 0, array.length);
    }

    private static void swap(int[] array, int i, int j) {
        int tmp = array[i];
        array[i] = array[j];
        array[j] = tmp;
    }

    public static void main(String[] args) {
        //int[] a = new int[]{5, 3, 7, 2};
        int[] a = new int[]{209823, 1239124, 219281, 234124, 1231, 101239128, 213, 4, 2};
        BitSort.sort(a);
        System.out.println(Arrays.toString(a));
    }
}