public class ArrayUtils {
    /*@ requires array != null;
      @ ensures (\forall int i; 0 <= i < array.length; array[i] == null);
      @*/
    public void setNull(Object[] array) {
        for(int i = 0; i < array.length; ++i) {
            array[i] = null;
        }
    }

    /*@ requires array != null;
      @ requires (\forall int i; 0 <= i < array.length; array[i] >= 0);
      @ requires (\forall int i; 0 <= i < array.length; array[i] < 2147483647);
      @ ensures (\forall int i; 0 <= i < array.length; array[i] >= 0);
      @*/
    public void addOne(int[] array) {
        for(int i = 0; i < array.length; ++i) {
            array[i]++;
        }
    }


    /*@ requires array != null;
      @ requires x >= 0 && x < 10000;
      @ requires (\forall int i; 0 <= i < array.length; array[i] >= 0);
      @ requires (\forall int i; 0 <= i < array.length; array[i] <= 2147483647 - x);
      @ ensures (\forall int i; 0 <= i < array.length; array[i] >= 0);
      @*/
    public void addX(int[] array, int x) {
        for(int i = 0; i < array.length; ++i) {
            array[i] += x;
        }
    }

}