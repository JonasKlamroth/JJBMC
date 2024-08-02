public class SelectionSort {

    /*@  normal_behavior
        requires a != null;
        ensures (\forall int i; 0 <= i && i < a.length - 1; a[i] <= a[i + 1]);
        assignable a[*];
    */
    public void sort(int[] a) {
        {
            /*@
                loop_invariant 0 <= i && i <= a.length;
                loop_invariant (\forall int j; 0 <= j && j < i; (\forall int k; j < k && k < a.length; a[j] <= a[k]));
                decreases a.length - i;
                assignable a[*];
            */
            for (int i = 0; i < a.length; i++) {
                int m = min(a, i);
                swap(a, m, i);
            }
        }
    }

    /*@  normal_behavior
        requires 0 <= i && i < a.length;
        requires 0 <= j && j < a.length;
        ensures \old(a[i]) == a[j];
        ensures \old(a[j]) == a[i];
        assignable a[i], a[j];
    */
    public void swap(int[] a, int i, int j) {
        int temp = a[i];
        a[i] = a[j];
        a[j] = temp;
    }

    /*@  normal_behavior
        requires 0 <= start && start < a.length;
        ensures (\forall int i; start <= i && i < a.length; a[\result] <= a[i]);
        ensures start <= \result && \result < a.length;
        assignable \nothing;
    */
    public int min(int[] a, int start) {
        int res = start;
        {
            /*@
                loop_invariant start <= i && i <= a.length;
                loop_invariant start <= res && res < a.length;
                loop_invariant (\forall int j; start <= j && j < i; a[res] <= a[j]);
                decreases a.length - i;
                assignable \nothing;
            */
            for (int i = start; i < a.length; i++) {
                if (a[i] < a[res]) {
                    res = i;
                }
            }
        }
        return res;
    }
}