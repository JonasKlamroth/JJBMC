class HeapSort {

    //@      public normal_behaviour
    //@        requires a != null;
    //@        ensures (\forall int i; 0 <= i < a.length - 1; a[i] <= a[i+1]);
    //+KeY@    ensures \dl_seqPerm(\old(\dl_array2seq(a)), \dl_array2seq(a));
    //@        assignable a[*];
    public static void heapSort(int[] a) {

        if(a.length <= 1)
            return;

        heapify(a);
        //@ assume (\forall int i; 0 <=i<a.length; 0<=a[i]<5);

        // @ loop_invariant 0 <= t <= a.length;
        // @ loop_invariant (\forall int i; t <= i < a.length - 1; a[i] <= a[i+1]);
        // @ loop_invariant t > 0 ==> a[0] >= a[t];
        // @ loop_invariant (\forall int i; 0<=i<a.length; 2*i+1 < t ==> a[i] >= a[2*i+1]);
        // @ loop_invariant (\forall int i; 0<=i<a.length; 2*i+2 < t ==> a[i] >= a[2*i+2]);
        // @ decreases t;
        for(int t = a.length-1; t > 0; t--) {
            popMax(a, t);
            //@ assume (\forall int i; 0 <=i<a.length; 0<=a[i]<5);
        }
    }

    //@      private normal_behaviour
    //@        requires a != null;
    //@        ensures (\forall int i; 0<=i<a.length; 2*i+1 < a.length ==> a[i] >= a[2*i+1]);
    //@        ensures (\forall int i; 0<=i<a.length; 2*i+2 < a.length ==> a[i] >= a[2*i+2]);
    //+KeY@    ensures \dl_seqPerm(\old(\dl_array2seq(a)), \dl_array2seq(a));
    //@        assignable a[*];
    private static void heapify(int[] a) {

        //@ assume false;

    }

    //@      private normal_behaviour
    //@        requires a != null;
    //@        requires 0 <= t < a.length;
    //@        requires (\forall int i; 0<=i<a.length; 2*i+1 < t ==> a[i] >= a[2*i+1]);
    //@        requires (\forall int i; 0<=i<a.length; 2*i+2 < t ==> a[i] >= a[2*i+2]);
    //@        ensures (\forall int i; 0<=i<a.length; 2*i+1 < t-1 ==> a[i] >= a[2*i+1]);
    //@        ensures (\forall int i; 0<=i<a.length; 2*i+2 < t-1 ==> a[i] >= a[2*i+2]);
    //@        ensures a[t] == \old(a[0]);
    //@        ensures a[0] == \old(a[t]);
    //+KeY@    ensures \dl_seqPerm(\old(\dl_array2seq(a)), \dl_array2seq(a));
    //@        assignable a[0..t];
    private static void popMax(int[] a, int t) {

        //@ assume false;

    }

}