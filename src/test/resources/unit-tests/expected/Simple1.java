public class Simple1 {

    public void foo() {
        {
            CProver.assume(A);
        }
        try {
        } catch (ReturnExc returnExc) {
        }
        {
            CProver.assert(B);
        }
    }

    public int fooInt() {
        {
            CProver.assume(C);
        }
        int __RESULT__;
        try {
        } catch (ReturnExc returnExc) {
        }
        {
            CProver.assert(D);
        }
        return __RESULT__;
    }

    @javax.annotation.processing.Generated("JJBMC")
    public final void fooContract() {
        {
            CProver.assert(A);
        }
        void __RESULT__;
        CProver.havoc(\nothing);
        {
            CProver.assume(B);
        }
        return __RESULT__;
    }

    @javax.annotation.processing.Generated("JJBMC")
    public final int fooIntContract() {
        {
            CProver.assert(C);
        }
        int __RESULT__;
        CProver.havoc(\nothing);
        {
            CProver.assume(D);
        }
        return __RESULT__;
    }
}

@javax.annotation.processing.Generated("JJBMC")
class ReturnException extends Exception {
}
