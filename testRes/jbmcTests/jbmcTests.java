import org.cprover.CProver;

public class jbmcTests{
    jbmcTests t = null;
    jbmcTests t2 = null;

    public void test2(){
        jbmcTests local = new jbmcTests();
         = Prover.nondetWithNull();
        assert local!=t;
    }

    public void test3(){
         = ew jbmcTests();
        t = Prover.nondetWithNull();
        assert t2!=t;
    }
}
