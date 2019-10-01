
import org.cprover.CProver;

public class ArrayMax {
  
  public ArrayMax() {
    try {
    } catch (ArrayMax.ReturnException ex) {
    }
  }
    /*@
    public behavior
      assignable \nothing; 
      signals () false; 
   */

  public static ArrayMax ArrayMaxSymb() {
    return new ArrayMax();
  }
  
  public int max(/*@ non_null */ 
  int[] a, int b) {
    {
      CProver.assume(a != null);
    }
    {
      CProver.assume(a.length < 5);
    }
    int returnVar = 0;
    try {
      if (a.length == 0) {
        returnVar = 0;
        throw new ArrayMax.ReturnException();
      }
      int max = a[1];
      int i = 1;
      while (i < a.length) {
        if (a[i] > max) max = a[i];
        ++i;
      }
      {
        returnVar = max;
        throw new ArrayMax.ReturnException();
      }
    } catch (ArrayMax.ReturnException ex) {
    }
    {
      int quantVar0j = CProver.nondetInt();
      assert (!(quantVar0j >= 0 && quantVar0j < a.length) || returnVar >= a[quantVar0j]);
    }
    {
      boolean b_0 = false;
      if (!!(a.length > 0)) {
        for (int quantVar0j = 0; quantVar0j >= 0 && quantVar0j < a.length; ++quantVar0j) {
          b_0 = b_0 || returnVar == a[quantVar0j];
        }
      }
      assert !(a.length > 0) || (b_0);
    }
    return returnVar;
  }
  
  class ReturnException extends java.lang.RuntimeException {
  }
}
