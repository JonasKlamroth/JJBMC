public class ArraySetNull {
    /*@ requires array != null;
      @ ensures (\forall int i; 0 <= i < array.length; array[i] == null);
      @*/
    public void setNull(Object[] array) {
        for(int i = 0; i < array.length; ++i) {
            array[i] = null;
            if(i == 19) {
                array[i] = new Object();
            }
        }
    }
}