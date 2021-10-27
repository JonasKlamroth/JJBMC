package CaseStudy;

class DualPivotQuicksort {

    static int less, great;
    static int e1,e2,e3,e4,e5;

    /*@
      @ requires a != null && a.length <= 5;
      @ requires 0 <= left && right < a.length;
      @ requires left == less && less < great && great < a.length;
      @ requires (\exists int j; less+1 <= j && j < great; a[j] >= pivot1);
      @ ensures less < great;
      @ ensures (\forall int i; left < i && i < less; a[i] < pivot1);
      @ ensures a[less] >= pivot1;
      @ ensures \old(less) < less;
      @ assignable less;
      @*/
    static void  move_less_right(int[] a, int left, int right, int pivot1) {
        /*@
          @ loop_invariant
          @     0 <= less && less <= great && great < a.length
          @  && (\forall int i; left < i && i < less+1; a[i] < pivot1)
          @  && (\exists int j; less+1 <= j && j < great; a[j] >= pivot1)
          @  && \old(less) <= less;
          @  loop_modifies less;
          @  decreases great - less;
          @*/
        while (a[++less] < pivot1) {
        }
    }




    /*@
      @ requires a != null && a.length <= 5;
      @ requires 0 <= left && left <= less && less < great && great == right && right < a.length;
      @ requires (\exists int i; less <= i && i < great; a[i] <= pivot2);
      @ ensures less <= great;
      @ ensures (\forall int i; great < i && i < right; a[i] > pivot2);
      @ ensures a[great] <= pivot2;
      @ ensures great < \old(great);
      @ assignable great;
      @*/
    static void move_great_left(int[] a, int left, int right, int pivot2) {
      /*@
        @ loop_invariant great > 0;
        @ loop_invariant left <= great && great <= right;
        @ loop_invariant less <= great;
        @ loop_invariant (\forall int i; great-1 < i && i < right; a[i] > pivot2);
        @ loop_invariant (\exists int j; less <= j && j < great; a[j] <= pivot2);
        @ decreases great;
        @ loop_modifies great;
        @*/
        while (a[--great] > pivot2) {
        }
    }


    /*@
      @ requires a != null && a.length <= 5 && left >= 0;
      @ requires 0 <= k && k <= great && great < a.length;
      @ requires (\exists int i; left <= i && i <= great; a[i] <= pivot2);
      @ ensures 0 <= great;
      @ ensures (\forall int i; great < i && i <= \old(great); a[i] > pivot2);
      @ ensures a[great] <= pivot2 || great == k;
      @ ensures k <= great && great <= \old(great);
      @ assignable great;
      @*/
    static void move_great_left_in_loop(int[] a, int k, int left, int right, int pivot2) {
        while (a[great] > pivot2 && great != k) {
            --great;
        }
    }

    /*@
      @ requires 0 <= left && left < right && right - left >= 46 && left <= 10000 && right <= 10000;
      @ ensures left < e1 && e1 < e2 && e2 < e3 && e3 < e4 && e4 < e5 && e5 < right;
      @ assignable e1,e2,e3,e4,e5;
      @*/
    static void calcE(int left, int right) {
        int length = right - left + 1;
        int seventh = (length >> 3) + (length >> 6);
        seventh++;
        e3 = (left + right) >>> 1; // The midpoint
        e2 = e3 - seventh;
        e1 = e2 - seventh;
        e4 = e3 + seventh;
        e5 = e4 + seventh;
    }
}
