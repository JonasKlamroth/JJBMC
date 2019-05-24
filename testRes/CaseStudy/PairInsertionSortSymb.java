package CaseStudy;

import TestAnnotations.Verifyable;

/**
 * Created by jklamroth on 2/20/19.
 */
public class PairInsertionSortSymb {
    /*@ requires a != null && a.length <= 5;
      @ requires 0 < left && left <= right && right < a.length;
      @ //requires right - left + 1 < 47;
      @ requires (\forall int i; left - 1 <= i && i <= right; a[left - 1] <= a[i]);
      @ assignable a[left..right];
      @ ensures (\forall int i; \old(left) - 1 <= i && i < \old(right); a[i] <= a[i + 1]);
      @*/
    @Verifyable
    public static void sort(int[] a, int left, int right) {

	/*@ loop_invariant right == \old(right) && \old(left) <= \old(right);
	  @ loop_invariant right == \old(right);
	  @ loop_invariant k == left;
	  @ loop_invariant \old(left) <= k && k <= \old(right) + (\old(right) - \old(left)) % 2;
	  @ loop_invariant (left - \old(left)) % 2 == 0;
	  @ loop_invariant (\old(right) + 2 - left) % 2 == (\old(right) - \old(left)) % 2;
	  @ loop_invariant (\forall int v; \old(left) - 1 <= v && v <= \old(right); a[\old(left) - 1] <= a[v]);
	  @ loop_invariant (\forall int j; \old(left) - 1 <= j && j < left - 1; a[j] <= a[j + 1]);
	  @ loop_modifies a[left..(right - 1 + (right - left) % 2)], left, k;
	  @ decreases \old(right) + 1 - left;
	  @*/
        for (int k = left; ++left <= right; k = ++left) {
            int a1 = a[k];
            int a2 = a[left];

            if (a1 < a2) {
                a2 = a1;
                a1 = a[left];
            }

	    /*@ loop_invariant right == \old(right) && \old(left) <= \old(right) && \old(left) < left && k < left;
	      @ loop_invariant right == \old(right);
	      @ loop_invariant \old(left) <= k && left <= \old(right) - 1 + (\old(right) - \old(left)) % 2 && k <= \old(right) - 2 + (\old(right) - \old(left)) % 2;
	      @ loop_invariant (\forall int t; \old(left) - 1 <= t && t <= \old(right); a[\old(left) - 1] <= a[t]);
	      @ loop_invariant a[\old(left) - 1] <= a1;
	      @ loop_invariant a2 <= a1;
	      @ loop_invariant (\forall int i; \old(left) - 1 <= i && i < k - 1; a[i] <= a[i + 1]);
	      @ loop_invariant \old(left) <= k && k < left - 1 ==> a[k - 1] <= a[k + 2];
	      @ loop_invariant \old(left) - 1 <= k && k < left - 1 ==> a[k] <= a[k + 2];
	      @ loop_invariant (\forall int j; k + 2 <= j && j < left; a[j] <= a[j + 1]);
	      @ loop_invariant (\forall int n; k <= n && n < left - 1; a1 < a[n]);
	      @ loop_invariant (\forall int m; k + 2 <= m && m <= left; a1 < a[m]);
	      @ loop_modifies a[(\old(left))+2..left], k;
	      @ decreases k;
	      @*/
            while (a1 < a[--k]) {
                a[k + 2] = a[k];
            }

            a[++k + 1] = a1;

	    /*@ loop_invariant right == \old(right) && \old(left) <= \old(right) && \old(left) < left && k < left;
	      @ loop_invariant right == \old(right);
	      @ loop_invariant \old(left) <= k && left <= \old(right) - 1 + (\old(right) - \old(left)) % 2 && k <= \old(right) - 2 + (\old(right) - \old(left)) % 2;
	      @ loop_invariant (\forall int s; \old(left) - 1 <= s && s <= \old(right); a[\old(left) - 1] <= a[s]);
	      @ loop_invariant a[\old(left) - 1] <= a2;
	      @ loop_invariant a2 <= a1;
	      @ loop_invariant (\forall int i; \old(left) - 1 <= i && i < k - 1; a[i] <= a[i + 1]);
	      @ loop_invariant \old(left) <= k && k < left ==> a[k - 1] <= a[k + 1];
	      @ loop_invariant (\forall int j; k + 1 <= j && j < left; a[j] <= a[j + 1]);
	      @ loop_invariant (\forall int n; k <= n && n < left - 1; a2 <= a[n]);
	      @ loop_invariant (\forall int m; k + 1 <= m && m <= left; a2 <= a[m]);
	      @ loop_invariant (\forall int l; k + 2 <= l && l <= left; a2 < a[l]);
	      @ loop_modifies a[(\old(left)+1)..left-1], k;
	      @ decreases k;
	      @*/
            while (a2 < a[--k]) {
                a[k + 1] = a[k];
            }

            a[k + 1] = a2;
        }

        int last = a[right];

	/*@ loop_invariant left == \old(right) + 1 + (\old(right) - \old(left)) % 2;
	  @ loop_invariant \old(left) <= right && right <= \old(right);
	  @ loop_invariant (\forall int q; \old(left) - 1 <= q && q <= \old(right); a[\old(left) - 1] <= a[q]);
	  @ loop_invariant a[\old(left) - 1] <= last;
	  @ loop_invariant (\forall int j; \old(left) - 1 <= j && j < right - 1; a[j] <= a[j + 1]);
	  @ loop_invariant \old(left) <= right && right < \old(right) ==> a[right - 1] <= a[right + 1];
	  @ loop_invariant (\forall int n; right + 1 <= n && n < \old(right); a[n] <= a[n + n]);
	  @ loop_invariant (\forall int m; right <= m && m < \old(right); last < a[m]);
	  @ loop_invariant right < \old(right) ==> a[right] <= a[right + 1];
	  @ loop_modifies a[(\old(left))+1..(\old(right))], right;
	  @ decreases right;
	  @*/
        while (last < a[--right]) {
            a[right + 1] = a[right];
        }

        a[right + 1] = last;
    }
}
