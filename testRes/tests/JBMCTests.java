import java.util.ArrayList;

public class JBMCTests {
    JBMCTests t;
    JBMCTests t1 = null;
    int[] arr;
    ArrayList<String> l = new ArrayList<>();


    //fails since apparently default values are not considered
    public JBMCTests() {
        assert t == null;
    }

    //verifyable: this is expected i guess?
    public JBMCTests(ArrayList l1) {
        assert l != l1;
    }

    //fails due to not including the necessary library
    public void test() {
        ArrayList<String> l = new ArrayList<>();
        l.add("test");
        assert l.size() == 1;
    }

    //fails regardless of using == or != in the assertion which is expected
    public void test0(ArrayList l1) {
        assert l == l1; //neither == nor != works here
    }

    //verifyable (as expected)
    public void test1() {
        JBMCTests t1 = new JBMCTests();
        JBMCTests t2 = new JBMCTests();
        assert t1 != t2;
    }

    //verifyable (as expected)
    public void test1(JBMCTests t1) {
        JBMCTests t2 = new JBMCTests();
        assert t1 != t2;
    }

    //@ assignable t;
    void callee() {
        //this is just a dummy for the next method
    }

    //verifyable but unexpected. This should be able to alias
    public void test2() {
        JBMCTests local = new JBMCTests();
        //this is basically just a hack to get this.t to be a nondeterministic object.
        callee();
        assert local != t;
    }

    //same as the previous test but with a field instead of a locally created object. same result
    public void test3() {
        t1 = new JBMCTests();
        //this is basically just a hack to get this.t to be a nondeterministic object.
        callee();
        assert t1 != t;
    }

    //@ requires arr != null && arr.length > 5;
    //this is verifiable due to the hard coded maximal array length of 5 in JBMC
    private void arrayTest() {
       assert false;
    }
}
