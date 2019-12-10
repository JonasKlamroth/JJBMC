import org.cprover.CProver;

public class jbmcTests{
    jbmcTests t = null;
    jbmcTests t2 = null;

    public void test2(){
        jbmcTests local = new jbmcTests();
        t=CProver.nondetWithNull();
        assert local!=t;
    }

    public void test3(){
        t=new jbmcTests();
        t2=CProver.nondetWithNull();
        assert t2!=t;
    }
}
