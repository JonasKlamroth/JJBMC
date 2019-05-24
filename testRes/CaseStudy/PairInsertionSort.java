package CaseStudy;

import TestAnnotations.Unwind;
import TestAnnotations.Verifyable;

/**
 * This Pair Insertion Sort in which two elements are handled at a time
 * is used by Oracle's implementation of the Java Development Kit (JDK)
 * for sorting primitive values, where a is the array to be sorted, and
 * the integer variables left and right are valid indices into a that
 * set the range to be sorted.
 * This was the first challenge from the VerifyThis competition @ ETAPS 2017
 * organized by M. Huisman, R. Monahan, P. Müller, W. Mostowski,
 * and M. Ulbrich.
 * The specification considers only sortedness, the permutation property
 * is yet to be done.
 * @author Michael Kirsten <kirsten@kit.edu>
 */
public class PairInsertionSort {

    /*@ public normal_behaviour
      @ requires a != null && a.length < 5;
      @ requires 0 < left && left <= right && right < a.length;
      @ //requires right - left + 1 < 47;
      @ requires (\forall int i; left - 1 <= i && i <= right; a[left - 1] <= a[i]);
      @ assignable a[left..right];
      @ ensures (\forall int i; \old(left) - 1 <= i && i < \old(right); a[i] <= a[i + 1]);
      @*/
    @Unwind(number = 7)
    @Verifyable
    public static void sort(int[] a, int left, int right) {


        for (int k = left; ++left <= right; k = ++left) {
            int a1 = a[k];
            int a2 = a[left];

            if (a1 < a2) {
                a2 = a1;
                a1 = a[left];
            }

            while (a1 < a[--k]) {
                a[k + 2] = a[k];
            }
            a[++k + 1] = a1;
            while (a2 < a[--k]) {
                a[k + 1] = a[k];
            }

            a[k + 1] = a2;
        }
        int last = a[right];
        while (last < a[--right]) {
            a[right + 1] = a[right];
        }

        a[right + 1] = last;
    }
}
