//package sv_rac_solutions;

public class Queue {

    //@ public invariant 0 <= size && size <= arr.length;
    //@ public invariant 0 <= first && first < arr.length;
    //@ public invariant 0 <= next && next < arr.length;
    //@ public invariant first <= next ==> size == next - first;
    //@ public invariant first > next ==> size == next + arr.length - first;

    /*@ spec_public @*/ Object[] arr;
    /*@ spec_public @*/ int size;
    /*@ spec_public @*/ int first;
    /*@ spec_public @*/ int next;

    /*
      @ requires 0 < max;
      @ ensures arr.length == max;
      @ ensures size == 0;
      @ ensures arr != null;
      @ ensures 0 <= size && size <= arr.length;
      @ ensures 0 <= first && first < arr.length;
      @ ensures 0 <= next && next < arr.length;
      @ ensures first <= next ==> size == next - first;
      @ ensures first > next ==> size == next + arr.length - first;
      @*/
    Queue( int max ) {
        arr   = new Object[max];
        first = 0;
        next  = 0;
        size = 0;
    }

    /*@ requires arr != null;
      @ requires 0 <= size && size <= arr.length;
      @ requires 0 <= first && first < arr.length;
      @ requires 0 <= next && next < arr.length;
      @ requires first <= next ==> size == next - first;
      @ requires first > next ==> size == next + arr.length - first;
      @ ensures \result == size;
      @ ensures arr != null;
      @ ensures 0 <= size && size <= arr.length;
      @ ensures 0 <= first && first < arr.length;
      @ ensures 0 <= next && next < arr.length;
      @ ensures first <= next ==> size == next - first;
      @ ensures first > next ==> size == next + arr.length - first;
      @*/
    public /*@pure */ int size() {
        return size;
    }


    //  invariant not perserved: ensures first <= next ==> size == next - first;
    // counter example: first = 1, next = 0, size = 1, arr.length = 2
    /*@ requires arr != null;
      @ requires arr.length > 1 && arr.length <= 5;
      @ requires 0 <= size && size <= arr.length;
      @ requires 0 <= first && first < arr.length;
      @ requires 0 <= next && next < arr.length;
      @ requires first <= next ==> size == next - first;
      @ requires first > next ==> size == next + arr.length - first;
      @ requires size < arr.length;
      @ ensures arr[\old(next)] == x;
      @ ensures next == (\old(next) + 1) % arr.length;
      @ ensures first == \old(first);
      @ ensures arr != null;
      @ ensures 0 <= size && size <= arr.length;
      @ ensures 0 <= first && first < arr.length;
      @ ensures 0 <= next && next < arr.length;
      @ ensures first > next ==> size == next + arr.length - first;
      @*/
    public void enqueue1( Object x ) {
        arr[next] = x;
        next = (next + 1) % arr.length;
        size++;
    }

    /*@ requires arr != null;
      @ requires 0 <= size && size <= arr.length;
      @ requires 0 <= first && first < arr.length;
      @ requires 0 <= next && next < arr.length;
      @ requires first <= next ==> size == next - first;
      @ requires first > next ==> size == next + arr.length - first;
      @ requires size > 0;
      @ ensures \result == arr[\old(first)];
      @ ensures first == (\old(first) + 1) % arr.length;
      @ ensures next == \old(next);
      @ ensures arr != null;
      @ ensures 0 <= size && size <= arr.length;
      @ ensures 0 <= first && first < arr.length;
      @ ensures 0 <= next && next < arr.length;
      @ ensures first <= next ==> size == next - first;
      @ ensures first > next ==> size == next + arr.length - first;
	  @*/
    public Object dequeue() {
        Object r = arr[first];
        first = (first + 1) % arr.length;
        size--;
        return r;
    }


//    public static void main(String[] args) {
//        Queue q = new Queue(10);
//        q.enqueue(new Object());
//        q.enqueue(new Object());
//        q.enqueue(new Object());
//        q.enqueue(new Object());
//        Object o = q.dequeue();
//        o = q.dequeue();
//        o = q.dequeue();
//    }
}