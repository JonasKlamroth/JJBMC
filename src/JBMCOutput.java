import com.sun.tools.javac.util.Pair;

import java.util.*;
import java.util.stream.Collectors;

public class JBMCOutput {
    public String proverStatus = "";
    public List<String> messages = new ArrayList<>();
    public List<String> errors = new ArrayList<>();
    public List<String> properties = new ArrayList<>();
    public List<String> reasons = new ArrayList<>();
    public List<List<Assignment>> traces = new ArrayList<>();
    public List<Integer> lineNumbers = new ArrayList<>();
    public List<String> failingLines = new ArrayList<>();

    public void addProperty(String name, List<Assignment> trace, int lineNumber, String failingLine, String reason) {
        properties.add(name);
        traces.add(trace);
        lineNumbers.add(lineNumber);
        failingLines.add(failingLine);
        reasons.add(reason);
    }

    public static class Assignment {
        public int lineNumber;
        public String jbmcVarname;
        public String value;
        public String guess;

        public Assignment(int line, String jbmcVarname, String guess, String value) {
            this.lineNumber = line;
            this.jbmcVarname = jbmcVarname;
            this.value = value;
            if (guess != null && guess.isEmpty()) {
                this.guess = null;
            } else {
                this.guess = guess;
            }
        }

        public Assignment(String line, String jbmcVarname, String guess, String value) {
            this(Integer.parseInt(line), jbmcVarname, guess, value);
        }

        @Override
        public String toString() {
            return "in line " + lineNumber + ": " + guess + " = " + value;
        }

        public String toString1() {
            return "in line " + lineNumber + ": " + jbmcVarname + " = " + value;
        }
    }

    private List<Assignment> filterTrace(List<Assignment> trace) {
        List<Assignment> newTrace = new ArrayList<>();
        trace = trace.stream().filter(x -> x.guess != null).collect(Collectors.toList());
        for(int i = trace.size() - 1; i >= 0; --i) {
            int finalI = i;
            List<Assignment> finalTrace = trace;
            if(!newTrace.stream().anyMatch(x -> x.guess.equals(finalTrace.get(finalI).guess))) {
                 newTrace.add(trace.get(i));
             }
        }
        Collections.reverse(newTrace);
        return newTrace;
    }
    public void printTrace(String property, boolean printGuesses) {
        int idx = properties.indexOf(property);
        if(idx == -1) {
            return;
        }
        List<Assignment> trace = traces.get(idx);
        if(trace == null) {
            return;
        }

        System.out.println("Trace for PVC: " + property + " in line " + lineNumbers.get(idx));
        List<Assignment> filteredTrace = filterTrace(trace);
        if(printGuesses) {
            for (Assignment a : filteredTrace) {
                System.out.println(a);
            }
        } else {
            for (Assignment a: filteredTrace) {
                a.toString1();
            }
        }
        System.out.println("Fail in line " + lineNumbers.get(idx) + ":" + failingLines.get(idx) + " (" + reasons.get(idx) + ")");
    }

    public void printTrace(String property) {
        printTrace(property, true);
    }

    public void printAllTraces() {
        for(String s : properties) {
            printTrace(s);
        }
    }

    public void printStatus() {
        System.out.println(proverStatus);
        if(errors.size() > 0) {
            for(String error : errors) {
                System.out.println(error);
            }
        }
    }
}
