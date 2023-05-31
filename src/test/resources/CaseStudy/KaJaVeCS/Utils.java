public final class Utils {

    private Utils() { }
    

    /*@ public normal_behavior
      @ requires arr != null;
      @ ensures \result.length == arr.length;
      @ //ensures \fresh(\result) && \fresh(\result[*]);
      @ ensures (\forall int i; 0 <= i && i < arr.length; \result[i] == arr[i]);
      @ assignable \nothing;
      @*/
    public static final int[] cloneArray(int[] arr) {
        int[] result = new int[arr.length];
        int i = 0;
        /*KEY@ loop_invariant 0 <= i && i <= arr.length;
          @ loop_invariant (\forall int j; 0 <= j && j < i; result[j] == arr[j]);
          @ loop_invariant arr != null;
          @ decreases arr.length - i;
          @ assignable result[*];
          @*/
        while (i < arr.length) {
            result[i] = arr[i];
            ++i;
        }
        return result;
    }
    
    /*@ public normal_behavior
      @ requires arr != null;
      @ ensures \result == (\forall int i; 0 <= i && i < arr.length - 1; arr[i] <= arr[i + 1]);
      @ assignable \nothing;
      @*/
    public static final boolean isSorted(int[] arr) {
        boolean result = true;
        /*KEY@ loop_invariant 0 <= i && (i <= arr.length - 1 || arr.length <= 1 && i == 0);
          @ loop_invariant result == (\forall int j; 0 <= j && j < i; arr[j] <= arr[j + 1]);
          @ loop_invariant arr != null;
          @ decreases arr.length - i;
          @ assignable \nothing;
          @*/
        for (int i = 0; i < arr.length - 1; ++i) {
            if (arr[i] > arr[i + 1]) {
                result = false;
            }
        }
        return result;
    }
    
    public static final boolean isStrictlySorted(int[] arr) {
        boolean result = true;
        for (int i = 0; i < arr.length - 1; ++i) {
            if (arr[i] >= arr[i + 1]) {
                result = false;
            }
        }
        return result;
    }
    
    /*@ public normal_behavior
      @ requires arr != null;
      @ ensures \result == (\forall int i; 0 <= i && i < arr.length; arr[i] >= 0);
      @ assignable \nothing;
      @*/
    public static final /*@ pure */ boolean isNonNegative(int[] arr) {
        boolean result = true;
        /*+KEY@ loop_invariant 0 <= i && i <= arr.length;
          @ loop_invariant result == (\forall int j; 0 <= j && j < i; arr[j] >= 0);
          @ loop_invariant arr != null;
          @ decreases arr.length - i;
          @ assignable \nothing;
          @*/
        for (int i = 0; i < arr.length; ++i) {
            if (arr[i] < 0) {
                result = false;
            }
        }
        return result;
    }
    
    public static final boolean isPositive(int[] arr) {
        boolean result = true;
        for (int i = 0; i < arr.length; ++i) {
            if (arr[i] <= 0) {
                result = false;
            }
        }
        return result;
    }
    
    public static final boolean isNonPositive(int[] arr) {
        boolean result = true;
        for (int i = 0; i < arr.length; ++i) {
            if (arr[i] > 0) {
                result = false;
            }
        }
        return result;
    }
    
    public static final boolean isNegative(int[] arr) {
        boolean result = true;
        for (int i = 0; i < arr.length; ++i) {
            if (arr[i] >= 0) {
                result = false;
            }
        }
        return result;
    }
}
