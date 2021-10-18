import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;

/*
    This only prevents some error messages from being displayed.
     */
class CostumPrintStream extends PrintStream {
    static private boolean filtered = false;

    public CostumPrintStream(OutputStream out) {
        super(out);
    }

    @Override
    public void print(String s) {
        if(!s.startsWith("class ")) {
            if(s.contains("/tmp/")) {
                super.print(s.replaceAll("/tmp", ""));
            }
            if(s.contains("signals () false")) {
                return;
            }
            super.print(s);
        } else {
            filtered = true;
        }
    }

    @Override
    public void write(byte[] buf, int off, int len) {
        if(!filtered) {
            String s = new String(buf, StandardCharsets.UTF_8);
            if(s.contains("/tmp/")) {
                super.print(s.replaceAll("/tmp", ""));
            }
            if(s.contains("signals () false")) {
                return;
            }
            super.write(buf, off, len);
        } else {
            filtered = false;
        }
    }
}
