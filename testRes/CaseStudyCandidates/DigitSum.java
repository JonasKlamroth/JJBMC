class DigitSum {

    public int ds(int n) {
        return n < 10 ? n :
                n % 9 == 0 ? 9 : n % 9;
    }

    /*@ public normal_behaviour
      @ requires n >= 0;
      @ requires n < 1000000;
      @ ensures \result == ds(n);
      @ ensures 0 <= \result <= 9;
      @ assignable \nothing;
      @*/
    int digitSum(int n) {
        if(n < 10) {
            return n;
        } else {
            int m = digitSum(n / 10);
            int x = m + (n % 10);
            //@ assert 0 <= x <= 18;
            return x / 10 + x % 10;
        }
    }
}