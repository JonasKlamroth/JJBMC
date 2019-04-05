
import org.cprover.CProver;

final class SortingAlgorithms {
    /*@
    behavior
      assignable \nothing; 
      signals () false; 
   */

  /*@ pure */ 
  SortingAlgorithms() {
    super();
  }
  
  static void nanoInsertionSort(/*@ non_null */ 
  int[] a, int low, int high) {
    try {
      {
        CProver.assume(a != null && a.length <= 5);
      }
    } catch (java.lang.Exception e) {
      throw new java.lang.RuntimeException("Specification is not well defined for method nanoInsertionSort");
    }
    for (int k; ++low < high; ) {
      assert !false;
      k = low;
      int ak = a[k];
      while (ak < a[--k]) {
        assert !false;
        a[k + 1] = a[k];
      }
      assert !false;
      a[k + 1] = ak;
    }
    try {
      {
        int i = CProver.nondetInt();
        assert (!(low <= i && i < high - 2) || a[i] <= a[i + 1]);
      }
    } catch (java.lang.Exception e) {
      throw new java.lang.RuntimeException("Specification is not well defined for method nanoInsertionSort");
    }
  }
  
  static class ReturnException extends java.lang.RuntimeException {
  }
}