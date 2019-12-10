import java.util.ArrayList;

public class JBMCTests {
    JBMCTests t = null;
    ArrayList<String> l = new ArrayList<>();
    public void test() {
        ArrayList<String> l = new ArrayList<>();
        l.add("test");
        assert l.size() == 1;
    }

    public JBMCTests() {
        assert t == null;
    }

    public JBMCTests(ArrayList l1) {
        assert l != l1;
    }

    public void test0(ArrayList l1) {
        assert l == l1; //neither == nor != works here
    }

    public void test1() {
        JBMCTests t1 = new JBMCTests();
        JBMCTests t2 = new JBMCTests();
        assert t1 != t2;
    }

    public void test1(JBMCTests t1) {
        JBMCTests t2 = new JBMCTests();
        assert t1 != t2;
    }

    //@ assignable t;
    void callee() {
    }

    public void test2() {
        JBMCTests local = new JBMCTests();
        callee();
        assert local != t;
    }
}
