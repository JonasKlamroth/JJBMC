public class Shop {
    public /*@nullable@*/ java.lang.String[] productNames;

    public /*@nullable@*/ ImmutableArray productPrices;


    /*@ public behavior
      @*/
    public Shop() {
        super();

        java.lang.String[] temp0 = new String[]{"Apple", "Banana", "Cherry", "Date", "Elderberry", "Fig", "Grapefruit", "Huckleberry", "Iyokan", "Jackfruit", "Kumquat", "Lemon", "Mandarine", "Nectarine", "Orange", "Peach", "Quince", "Raspberry", "Strawberry", "Tangerine", "Ugli", "Vanilla", "Watermelon", "Ximenia", "Yuzu", "Zwetschge"};
        productNames = temp0;
        int[] tmp = new int[]{3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3, 2, 3, 8, 4, 6, 2, 6, 4, 3, 3};
        assert Utils.isNonNegative(tmp);
        ImmutableArray temp1 = ImmutableArray.__INIT_trampoline(tmp).__sortNonNegative_trampoline(false);
        //@ assume (true) && (temp1 != null && temp1.arr != null && Utils.isNonNegative(temp1.arr));
        //@ assume (true) && (temp1 != null && temp1.arr != null && Utils.isSorted(temp1.arr));
        productPrices = temp1;
    }

    /*@ public behavior
      @ ensures \result != null;
      @*/
    public static /*@nullable@*/ Shop __INIT_trampoline() {
        return new Shop();
    }


    /*@ public behavior
      @ assignable \nothing;
      @*/
    public /*@nullable@*/ String[] getProductNames() {
        java.lang.String[] temp2 = productNames;
        return temp2;
    }

    /*@ public behavior
      @*/
    public /*@nullable@*/ java.lang.String[] __getProductNames_trampoline() {
        return getProductNames();
    }


    /*@ public behavior
      @ ensures (true) && (\result != null && \result.arr != null && Utils.isNonNegative(\result.arr));
      @ ensures (true) && (\result != null && \result.arr != null && Utils.isSorted(\result.arr));
      @ assignable \nothing;
      @*/
    public /*@nullable@*/ ImmutableArray getProductPrices() {
        ImmutableArray temp3 = productPrices;
        //@ assume (true) && (temp3 != null && temp3.arr != null && Utils.isNonNegative(temp3.arr));
        //@ assume (true) && (temp3 != null && temp3.arr != null && Utils.isSorted(temp3.arr));
        return temp3;
    }

    /*@ public behavior
      @*/
    public /*@nullable@*/ ImmutableArray __getProductPrices_trampoline() {
        return getProductPrices();
    }

}