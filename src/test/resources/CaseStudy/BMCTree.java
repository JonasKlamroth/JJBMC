package de.wiesler;

public final class BMCTree {
    private  /*@ spec_public @*/ final int[] tree;

    // The following should be a ghost field: Can JJBMC do this?
    private  /*@ spec_public @*/ final int[] sorted_splitters;

    private  final int log_buckets;

    /*@ private invariant
      @ tree != null && sorted_splitters != null;
      @*/

    /*@ private invariant
      @ tree.length  == sorted_splitters.length + 1;
      @*/

    /*@ private invariant tree.length == 1 << log_buckets; */
    /*@ private invariant log_buckets > 1 && log_buckets <= 6; */

    /*@ private invariant
      @  (\forall int i; 1 <= i < tree.length;
      @    tree[i] == sorted_splitters[pi(i) - 1]);
      @*/



    /*@ private normal_behaviour
      @ requires tree != null && sorted_splitters != null;
      @  requires tree.length == sorted_splitters.length + 1;
      @  requires tree.length == 1 << log_buckets;
      @  requires log_buckets >= 0 && log_buckets <= 6;
      @*/
    public BMCTree(int[] sorted_splitters, int[] tree, int log_buckets) {
        this.sorted_splitters = sorted_splitters;
        this.log_buckets = log_buckets;
        this.tree = tree;
        this.build(1, sorted_splitters, 0, 42);
    }

    /*@ private normal_behaviour
      @  assignable \nothing;
      @*/
    private /*@ helper */ void build(int position, int[] sorted_splitters, int begin, int end) {
        final int mid = begin + (end - begin) / 2;
        this.tree[position] = sorted_splitters[mid];
        if (2 * position + 1 < (1 << this.log_buckets)) {
            this.build(2 * position, sorted_splitters, begin, mid);
            this.build(2 * position + 1, sorted_splitters, mid, end);
        }
    }

    /*@ pure */
    public int pi(int b) {
        int r = (2 * (b - (1 << log2(b))) + 1) * (1 << (log_buckets - 1 - log2(b)));
        return r;
    }

    /*@ pure */
    public int log2(int b) {
        if(b <= 1) return 0;
        else return 1 + log2(b/2);
    }

    /*@ private normal_behaviour
      @ //requires \invariant_for(this); // is this default in JJBMC?
      @
      @ ensures 0 <= \result <= sorted_splitters.length;
      @
      @ ensures \result < sorted_splitters.length ==> value <= sorted_splitters[\result];
      @
      @ ensures \result > 0 ==> value > sorted_splitters[\result - 1];
      @ assignable \nothing;
      @*/
    int classify(int value) {
        int b = 1;

        for (int i = 0; i < this.log_buckets; ++i) {
            b = 2 * b + (this.tree[b] < value ? 1 : 0);
        }

        return b - (1 << this.log_buckets);
    }

    public static void main(String[] args) {
        BMCTree t = new BMCTree(new int[]{0, 0, 0}, new int[]{0, 0}, 1);
        System.out.println(t.tree.length);
        System.out.println(1 << t.log_buckets);
        for(int i = 0; i < t.tree.length; i++) {
            System.out.println("i = " + i);
            System.out.println(t.pi(i));
        }
    }
}