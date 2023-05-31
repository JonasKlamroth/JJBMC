public class Simple1 {
    /*@ ensures A; requires B; assignable \nothing; */
    public void foo() {}

    /*@ ensures C; requires D; assignable \nothing; */
    public int fooInt() {}
}