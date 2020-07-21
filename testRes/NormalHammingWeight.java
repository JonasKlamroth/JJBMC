/**
 * Created by jklamroth on 1/8/19.
 */

class NormalHammingWeight {

  /*@  requires a != null;
    @  requires a.length <= 5;
    @  ensures \result <= a.length * 32;
    @  assignable \nothing;
    @*/
  int weight(int[] a) {
    int result = 0;
    //@ loop_invariant result <= i * 32;
    //@ loop_invariant 0 <= i && i <= a.length;
    //@ loop_modifies result;
    for (int i = 0; i < a.length; i++) {
      int x = a[i];
      x = x - ((x >>> 1) & 0x55555555);
      x = (x & 0x33333333) + ((x >>> 2) & 0x33333333);
      x = (x + (x >>> 4)) & 0x0f0f0f0f;
      x = x + (x >>> 8);
      x = x + (x >>> 16);
      result += (x & 0x3f);
    }
    return result;
  }

  /*@  requires a != null;
    @  requires a.length <= 5;
    @  ensures \result <= a.length * 32;
    @  assignable \nothing;
    @*/
  int weight3(int[] a) {
    int result = 0;
    for (int i = 0; i < a.length; i++) {
      int x = a[i];
      x = x - ((x >>> 1) & 0x55555555);
      x = (x & 0x33333333) + ((x >>> 2) & 0x33333333);
      x = (x + (x >>> 4)) & 0x0f0f0f0f;
      x = x + (x >>> 8);
      x = x + (x >>> 16);
      result += (x & 0x3f);
    }
    return result;
  }

  /*@  requires a != null;
    @  requires a.length <= 5;
    @  ensures \result <= a.length * 32;
    @  assignable \nothing;
    @*/
  int weight2(int[] a) {
    int result = 0;
    //@ loop_invariant result <= i * 32;
    //@ loop_invariant 0 <= i && i <= a.length;
    //@ loop_modifies result;
    for (int i = 0; i < a.length; i++) {
      int x = a[i];
      while (x != 0) {
        result += x&1;
        x = x >>> 1;
      }
    }
    return result;
  }
}
