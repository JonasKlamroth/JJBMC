
import org.cprover.CProver;

public class Test2tmp {
    /*@
    public behavior
      assignable \nothing; 
      signals () false; 
   */

  /*@ pure */ 
  public Test2tmp() {
    super();
  }
  private int privInt = 0;
  public int pubInt;
  /*@ non_null */ 
  Test2tmp t2;
  /*@ non_null */ 
  int[] arr;
  
  private void tmptest(int i) {
    try {
      CProver.assume(true);
    } catch (java.lang.Exception e) {
      throw new java.lang.RuntimeException("Specification is not well defined for method tmptest");
    }
    {
      throw new Test2tmp.ReturnException();
    }
  }
  
  private void test() {
    try {
      CProver.assume(1 < 0);
    } catch (java.lang.Exception e) {
      throw new java.lang.RuntimeException("Specification is not well defined for method test");
    }
    int locInt = 0;
    locInt++;
    if (true) throw new java.lang.RuntimeException("Illegal assignment: privInt = 0");
    privInt = 0;
    System.out.println("This is just a test." + locInt);
    try {
      if (CProver.nondetBoolean()) {
        assert true;
      }
    } catch (java.lang.Exception e) {
      throw new java.lang.RuntimeException("Specification is not well defined for method test");
    }
  }
  
  public int test1(int i) {
    try {
      CProver.assume(i > 0);
    } catch (java.lang.Exception e) {
      throw new java.lang.RuntimeException("Specification is not well defined for method test1");
    }
    int returnVar = 0;
    try {
      {
        returnVar = i + 1;
        throw new Test2tmp.ReturnException();
      }
    } catch (Test2tmp.ReturnException ex) {
      try {
        if (CProver.nondetBoolean()) {
          assert i > 1;
        }
      } catch (java.lang.Exception e) {
        throw new java.lang.RuntimeException("Specification is not well defined for method test1");
      }
      return returnVar;
    }
  }
  
  public static void test2() {
    {
      System.out.println("empty");
    }
  }
  
  public void quantTest() {
    try {
      boolean b_0 = true;
      for (int i = 0 + 1; i > 0 && i < 10; ++i) {
        b_0 = b_0 && i > 0;
      }
      CProver.assume(b_0);
      int i = CProver.nondetInt();
      CProver.assume(i > 0 && i < 10);
      CProver.assume((i == 5));
    } catch (java.lang.Exception e) {
      throw new java.lang.RuntimeException("Specification is not well defined for method quantTest");
    }
    System.out.println("this is basically a lemma.");
  }
  
  public void quantTest2tmp() {
    try {
      boolean b_1 = true;
      for (int i = 0 + 1; i > 0 && i < 10; ++i) {
        boolean b_0 = true;
        for (int j = 10 + 1; j > 10 && j < 20; ++j) {
          b_0 = b_0 && j > i;
        }
        b_1 = b_1 && b_0;
      }
      CProver.assume(b_1);
      int i = CProver.nondetInt();
      CProver.assume(i > 0 && i < 10);
      boolean b_0 = true;
      for (int j = 10 + 1; j > 10 && i < 20; ++j) {
        b_0 = b_0 && j > i;
      }
      CProver.assume(b_1);
    } catch (java.lang.Exception e) {
      throw new java.lang.RuntimeException("Specification is not well defined for method quantTest2tmp");
    }
    System.out.println("this is basically a lemma.");
  }
  
  public void quantTest3() {
    try {
      boolean b_0 = true;
      for (int i = 0 + 1; i > 0 && i < 10; ++i) {
        b_0 = b_0 && 3 + 10 > i;
      }
      CProver.assume(b_0);
      int i = CProver.nondetInt();
      CProver.assume(i > 0 && i < 10);
      CProver.assume((3 + 10 > i));
    } catch (java.lang.Exception e) {
      throw new java.lang.RuntimeException("Specification is not well defined for method quantTest3");
    }
    System.out.println("this is basically a lemma.");
    try {
      if (CProver.nondetBoolean()) {
        int i = CProver.nondetInt();
        if (i > 0 && i < 10) assert (3 + 10 > i);
      }
      if (CProver.nondetBoolean()) {
        boolean b_0 = false;
        for (int i = 0 + 1; i > 0 && i < 10; ++i) {
          b_0 = b_0 || 3 + 10 > i;
        }
        assert b_0;
      }
    } catch (java.lang.Exception e) {
      throw new java.lang.RuntimeException("Specification is not well defined for method quantTest3");
    }
  }
  
  public void returnTest() {
    try {
    } catch (java.lang.Exception e) {
      throw new java.lang.RuntimeException("Specification is not well defined for method returnTest");
    }
    if (privInt == 0) {
      if (true) throw new java.lang.RuntimeException("Illegal assignment: privInt = 0");
      privInt = 0;
    }
  }
  
  public void loopTest() {
    try {
      CProver.assume(true);
    } catch (java.lang.Exception e) {
      throw new java.lang.RuntimeException("Specification is not well defined for method loopTest");
    }
    /*@ non_null */ 
    int[] arr = new int[10];
    int i = 0;
    {
      assert i >= 0;
      assert i > -1;
    }
    i = CProver.nondetInt();
    {
      int arrLength = arr.length;
      arr = CProver.nondetWithoutNull();
      CProver.assume(arr.length == arrLength);
    }
    for (int __tmpVar__ = 2; __tmpVar__ <= 4; ++__tmpVar__) {
      arr[__tmpVar__] = CProver.nondetInt();
    }
    {
      CProver.assume(i >= 0);
      CProver.assume(i > -1);
    }
    if (i < 10) {
      arr[i] = i;
      ++i;
      {
        assert i >= 0;
        assert i > -1;
      }
      CProver.assume(false);
    }
    try {
      if (CProver.nondetBoolean()) {
        assert false;
      }
    } catch (java.lang.Exception e) {
      throw new java.lang.RuntimeException("Specification is not well defined for method loopTest");
    }
  }
  
  public void loopTest1() {
    /*@ non_null */ 
    int[] arr = new int[10];
    int i = 0;
    {
      int j = CProver.nondetInt();
      if (j > 0 && j < 10) assert (j > -1);
      assert i > -1;
    }
    i = CProver.nondetInt();
    {
      int arrLength = arr.length;
      arr = CProver.nondetWithoutNull();
      CProver.assume(arr.length == arrLength);
    }
    for (int __tmpVar__ = 2; __tmpVar__ <= 4; ++__tmpVar__) {
      arr[__tmpVar__] = CProver.nondetInt();
    }
    {
      boolean b_0 = true;
      for (int j = 0 + 1; j > 0 && j < 10; ++j) {
        b_0 = b_0 && j > -1;
      }
      CProver.assume(b_0);
      CProver.assume(i > -1);
    }
    if (i < 10) {
      arr[i] = i;
      ++i;
      {
        int j = CProver.nondetInt();
        if (j > 0 && j < 10) assert (j > -1);
        assert i > -1;
      }
      CProver.assume(false);
    }
  }
  
  private void assignalbeTest() {
    privInt = 0;
  }
  
  private void assignalbeTest1(/*@ non_null */ 
  Test2tmp t3) {
    if (t2 != t3) throw new java.lang.RuntimeException("Illegal assignment: t3 = new Test2tmp()");
    t3 = new Test2tmp();
    if (t2 != t3) throw new java.lang.RuntimeException("Illegal assignment: t3.t2 = new Test2tmp()");
    t3.t2 = new Test2tmp();
    if (true) throw new java.lang.RuntimeException("Illegal assignment: privInt = 0");
    privInt = 0;
  }
  
  private void assignalbeTest2tmp() {
    if (true && (arr != arr || 1 > 5 || 1 < 5)) throw new java.lang.RuntimeException("Illegal assignment: arr[1] = 5");
    arr[1] = 5;
    if (true && (arr != arr || 5 > 5 || 5 < 5)) throw new java.lang.RuntimeException("Illegal assignment: arr[5] = 3");
    arr[5] = 3;
  }
  
  private void assignalbeTest3() {
    if (true && arr != arr) throw new java.lang.RuntimeException("Illegal assignment: arr[3] = 5");
    arr[3] = 5;
  }
  
  private void assignalbeTest4() {
    if (true && (arr != arr || 4 > arr.length || 4 < 3)) throw new java.lang.RuntimeException("Illegal assignment: arr[4] = 2");
    arr[4] = 2;
  }
  
  private void assignalbeTest41(/*@ non_null */ 
  int[] arr1) {
    if (true && (arr != arr1 || 4 > 3 || 4 < 1) && (arr != arr1 || 4 > 5 || 4 < 4)) throw new java.lang.RuntimeException("Illegal assignment: arr1[4] = 2");
    arr1[4] = 2;
  }
  
  private void assignalbeTest5(/*@ non_null */ 
  Test2tmp t3) {
    if (true) throw new java.lang.RuntimeException("Illegal assignment: t3 = new Test2tmp()");
    t3 = new Test2tmp();
    if (true && t3 != t2) throw new java.lang.RuntimeException("Illegal assignment: t3.pubInt = 5");
    t3.pubInt = 5;
    if (true && t3 != t2) throw new java.lang.RuntimeException("Illegal assignment: t3.t2 = new Test2tmp()");
    t3.t2 = new Test2tmp();
    if (true && t3 != t2) throw new java.lang.RuntimeException("Illegal assignment: t3.t2.pubInt = 10");
    t3.t2.pubInt = 10;
    if (true && t3 != t2) throw new java.lang.RuntimeException("Illegal assignment: t3.arr = new int[10]");
    t3.arr = new int[10];
    if (true && t3 != t2) throw new java.lang.RuntimeException("Illegal assignment: t3.arr[5] = 10");
    t3.arr[5] = 10;
  }
  
  private void assignalbeTest6(/*@ non_null */ 
  Test2tmp t3) {
    if (true) throw new java.lang.RuntimeException("Illegal assignment: t3 = new Test2tmp()");
    t3 = new Test2tmp();
    if (true) throw new java.lang.RuntimeException("Illegal assignment: t3.pubInt = 5");
    t3.pubInt = 5;
    if (true) throw new java.lang.RuntimeException("Illegal assignment: t3.t2 = new Test2tmp()");
    t3.t2 = new Test2tmp();
    if (true && t3 != t2) throw new java.lang.RuntimeException("Illegal assignment: t3.t2.pubInt = 10");
    t3.t2.pubInt = 10;
  }
  
  private void assignalbeTest7(/*@ non_null */ 
  Test2tmp t3) {
    if (true && (t2.arr != t3.arr || 5 > 4 || 5 < 4)) throw new java.lang.RuntimeException("Illegal assignment: t3.arr[5] = 10");
    t3.arr[5] = 10;
  }
  
  private void assignalbeTest8() {
    int i = 5;
    i = 10;
    if (i > 10) {
      i = 20;
    }
  }
  
  private void assignalbeTest9() {
    if (privInt > 10) {
      if (true) throw new java.lang.RuntimeException("Illegal assignment: privInt = 20");
      privInt = 20;
    }
  }
  
  private void t() {
    if (true) throw new java.lang.RuntimeException("Illegal assignment: t2 = new Test2tmp()");
    t2 = new Test2tmp();
    /*@ non_null */ 
    Test2tmp t3 = t2;
    t3.privInt = 5;
    System.out.println(t2.privInt);
  }
  
  public static void main(/*@ non_null */ 
  String[] args) {
    /*@ non_null */ 
    Test2tmp t = new Test2tmp();
    t.t();
  }
  
  static class ReturnException extends java.lang.RuntimeException {
  }
}