/**
 * @author Alexander Weigl
 * @version 1 (23.07.18)
 */
public class Test {
    public void test() {
        //@ set x = 2;
        Ivil.set("x", 2);
    }
}

class Ivil {
    static void set(String x, int i) {
    }
}