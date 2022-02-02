public class ImmutableArray  {
    public /*@nullable@*/ int[] arr;

    
    /*@ public behavior
      @ ensures (true) && (this != null && this.arr != null && Utils.isNonNegative(this.arr));
      @ ensures (true) && (this != null && this.arr != null && Utils.isSorted(this.arr));
      @ ensures this.arr != null && this.arr.length == 0;
      @ assignable \nothing;
      @ diverges true;
      @*/
    public ImmutableArray() {
        super();

        int[] temp0 = new int[0];
        this.arr = temp0;
    }

    /*@ public behavior
      @ ensures \result != null;
      @ ensures \result.arr != null && \result.arr.length == 0;
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ ImmutableArray __INIT_trampoline() {
        return new ImmutableArray();
    }

    
    /*@ public behavior
      @ requires arr != null;
      @ ensures this.arr != null;
      @ ensures this.arr.length == arr.length;
      @ ensures (\forall int i; 0 <= i && i < arr.length; this.arr[i] == arr[i]);
      @ assignable \nothing;
      @*/
    public ImmutableArray(/*@nullable@*/ int[] arr) {
        super();

        int[] temp1 = Utils.cloneArray(arr);
        this.arr = temp1;
    }

    /*@ public behavior
      @ ensures \result != null;
      @ requires arr != null;
      @ ensures \result.arr != null;
      @ ensures \result.arr.length == arr.length;
      @ ensures (\forall int i; 0 <= i && i < arr.length; \result.arr[i] == arr[i]);
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ ImmutableArray __INIT_trampoline(/*@nullable@*/ int[] arr) {
        return new ImmutableArray(arr);
    }

    
    /*@ public behavior
      @ assignable \nothing;
      @*/
    public int get(int index) {
        int temp2 = arr[index];
        return temp2;
    }

    /*@ public behavior
      @ assignable \nothing;
      @*/
    public int __get_trampoline(int index) {
        return get(index);
    }

    
    /*@ public behavior
      @ requires (true) && (this != null && this.arr != null && Utils.isNonNegative(this.arr));
      @ ensures (true) && (\result >= 0);
      @ assignable \nothing;
      @*/
    public int getNonNegative(int index) {
        int temp3 = arr[index];
        //@ assert (true) && (temp3 >= 0);
        return temp3;
    }

    /*@ public behavior
      @ requires this_sign || ((true) && (this != null && this.arr != null && Utils.isNonNegative(this.arr)));
      @ assignable \nothing;
      @*/
    public int __getNonNegative_trampoline(int index, boolean this_sign) {
        return getNonNegative(index);
    }

    
    /*@ public behavior
      @ requires (true) && (this != null && this.arr != null && Utils.isNonNegative(this.arr));
      @ ensures (true) && (\result != null && \result.arr != null && Utils.isNonNegative(\result.arr));
      @ ensures (true) && (\result != null && \result.arr != null && Utils.isSorted(\result.arr));
      @ diverges true;
      @*/
    public /*@nullable@*/ ImmutableArray sortNonNegative() {
        int[] newArr;
        int[] temp4 = Utils.cloneArray(arr);
        newArr = temp4;
        Quicksort.sort(newArr);
        ImmutableArray temp5 = ImmutableArray.__INIT_trampoline(newArr);
        //@ assert (true) && (temp5 != null && temp5.arr != null && Utils.isNonNegative(temp5.arr));
        //@ assert (true) && (temp5 != null && temp5.arr != null && Utils.isSorted(temp5.arr));
        return temp5;
    }

    /*@ public behavior
      @ requires this_sign || ((true) && (this != null && this.arr != null && Utils.isNonNegative(this.arr)));
      @*/
    public /*@nullable@*/ ImmutableArray __sortNonNegative_trampoline(boolean this_sign) {
        return sortNonNegative();
    }

    
    /*@ public behavior
      @ requires (true) && (newElement >= 0);
      @ requires (true) && (this != null && this.arr != null && Utils.isNonNegative(this.arr));
      @ requires (true) && (this != null && this.arr != null && Utils.isSorted(this.arr));
      @ ensures (true) && (\result != null && \result.arr != null && Utils.isNonNegative(\result.arr));
      @ ensures (true) && (\result != null && \result.arr != null && Utils.isSorted(\result.arr));
      @ diverges true;
      @*/
    public /*@nullable@*/ ImmutableArray insertSortedNonNegative(int newElement) {
        int[] newArr;
        int[] temp6 = new int[arr.length + 1];
        newArr = temp6;
        System.arraycopy(arr, 0, newArr, 0, arr.length);
        int temp7 = newElement;
        newArr[arr.length] = temp7;
        ImmutableArray temp8 = ImmutableArray.__INIT_trampoline(newArr).__sortNonNegative_trampoline(false);
        //@ assume (true) && (temp8 != null && temp8.arr != null && Utils.isNonNegative(temp8.arr));
        //@ assume (true) && (temp8 != null && temp8.arr != null && Utils.isSorted(temp8.arr));
        return temp8;
    }

    /*@ public behavior
      @ requires newElement_sign || ((true) && (newElement >= 0));
      @ requires this_sign || ((true) && (this != null && this.arr != null && Utils.isNonNegative(this.arr)));
      @ requires this_sorted || ((true) && (this != null && this.arr != null && Utils.isSorted(this.arr)));
      @*/
    public /*@nullable@*/ ImmutableArray __insertSortedNonNegative_trampoline(int newElement, boolean newElement_sign, boolean this_sign, boolean this_sorted) {
        return insertSortedNonNegative(newElement);
    }

    
    /*@ public behavior
      @ ensures (true) && (\result >= 0);
      @ assignable \nothing;
      @*/
    public int length() {
        int temp9 = arr.length;
        //@ assert (true) && (temp9 >= 0);
        return temp9;
    }

    /*@ public behavior
      @ assignable \nothing;
      @*/
    public int __length_trampoline() {
        return length();
    }
}
