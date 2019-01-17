import java.io.OutputStream;
import java.io.PrintStream;

/*
    This only prevents some error messages to be displayed.
     */
class CostumPrintStream extends PrintStream {
    static private boolean filtered = false;

    public CostumPrintStream(OutputStream out) {
        super(out);
    }

    @Override
    public void print(String s) {
        if(!s.startsWith("class ")) {
            super.print(s);
        } else {
            filtered = true;
        }
    }

    @Override
    public void write(byte[] buf, int off, int len) {
        if(!filtered) {
            super.write(buf, off, len);
        } else {
            filtered = false;
        }
    }
}
