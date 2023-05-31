package CaseStudy;


/**
 * Created by jklamroth on 2/20/19.
 */
public class PairInsertionSort {
    /*@ requires a != null && a.length < 5;
      @ requires 0 < left && left <= right && right < a.length;
      @ requires (\forall int i; left - 1 <= i && i <= right; a[left - 1] <= a[i]);
      @ assignable a[left..right];
      @ ensures (\forall int i; \old(left) - 1 <= i && i < \old(right); a[i] <= a[i + 1]);
      @*/
    public static void sort(int[] a, int left, int right) {

        left++;
        for (int k = left - 1; left <= right; k = ++left) {
            int a1 = a[k];
            int a2 = a[left];

            if (a1 < a2) {
                a2 = a1;
                a1 = a[left];
            }

            k--;
            while (a1 < a[k]) {
                a[k + 2] = a[k];
            }

            a[++k + 1] = a1;

            k--;
            while (a2 < a[k]) {
                a[k + 1] = a[k];
            }

            a[k + 1] = a2;
            left++;
        }

        int last = a[right];

        right--;
        while (last < a[right]) {
            a[right + 1] = a[right];
        }

        a[right + 1] = last;
    }
}
