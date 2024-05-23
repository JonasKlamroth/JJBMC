package jjbmc;

import java.io.File;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;

/*
    This only prevents some error messages from being displayed.
     */
public class CostumPrintStream extends PrintStream {
    private static boolean filtered = false;
    private static boolean active = true;

    public static void turnOff() {
        active = false;
    }

    public static void turnOn() {
        active = true;
    }

    public CostumPrintStream(OutputStream out) {
        super(out);
    }

    @Override
    public void print(String s) {
        if (active) {
            if (!s.startsWith("class ")) {
                if (s.contains(File.separator + "tmp" + File.separator)) {
                    super.print(s.replaceAll(File.separator + "tmp", ""));
                }
                if (s.contains("signals () false")) {
                    return;
                }
                super.print(s);
            } else {
                filtered = true;
            }
        }
    }

    @Override
    public void write(byte[] buf, int off, int len) {
        if (active) {
            if (!filtered) {
                String s = new String(buf, StandardCharsets.UTF_8);
                if (s.contains(File.separator + "tmp" + File.separator)) {
                    super.print(s.replace(File.separator + "tmp", ""));
                }
                if (s.contains("signals () false")) {
                    return;
                }
                super.write(buf, off, len);
            } else {
                filtered = false;
            }
        }
    }
}
