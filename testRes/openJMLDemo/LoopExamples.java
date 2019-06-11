public class LoopExamples {

    int [] a;


    LoopExamples() {
        a = new int[5];
    }

    //@ requires a != null;
    public void setA(int [] a) {
        this.a = a;
    }

    /*@ normal_behavior
        requires a != null && a.length <= 4;
        ensures \result == (\exists int i; 0 <= i && i < a.length; a[i] == x);
     */
    boolean contains(int x) {
        boolean found = false;
        //@ loop_invariant 0 <= i && i <= a.length;
        //@ loop_invariant (\exists int j; 0 <= j && j < i; a[j] == x) == found;
        //@ loop_modifies found;
        for (int i = 0; i < a.length; i++) {
            if (a[i] == x) {found = true;}
            else {}
        }
        return found;
    }


}