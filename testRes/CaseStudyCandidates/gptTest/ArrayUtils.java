public class ArrayUtils {
    /*@ requires array != null;
      @ ensures (\forall int i; 0 <= i < array.length; array[i] == null);
      @*/
    public void setNull(Object[] array) {
        /*@ maintaining 0 <= i <= array.length;
          @ maintaining (\forall int j; 0 <= j < i; array[j] == null);
          @ decreasing array.length - i;
          @*/
        for (int i = 0; i < array.length; ++i) {
            array[i] = null;
        }
    }
}
