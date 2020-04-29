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
            if(newTrace.stream().noneMatch(x -> x.guess.equals(finalTrace.get(finalI).guess))) {
                 newTrace.add(trace.get(i));
             }
        }
        Collections.reverse(newTrace);
        return newTrace;
    }
    public String printTrace(String property, boolean printGuesses) {
        StringBuilder sb = new StringBuilder();
        int idx = properties.indexOf(property);
        if(idx == -1) {
            return "";
        }
        List<Assignment> trace = traces.get(idx);
        if(trace == null) {
            return "";
        }

        sb.append("Trace for PVC: " + property + " in line " + lineNumbers.get(idx) + "\n");
        List<Assignment> filteredTrace = filterTrace(trace);
        if(printGuesses) {
            for (Assignment a : filteredTrace) {
                sb.append(a + "\n");
            }
        } else {
            for (Assignment a: filteredTrace) {
                sb.append(a.toString1() + "\n");
            }
        }
        sb.append("Fail in line " + lineNumbers.get(idx) + ":" + failingLines.get(idx) + " (" + reasons.get(idx) + ")\n");
        return sb.toString();
    }

    public String printTrace(String property) {
        return printTrace(property, true);
    }

    public String printErrors() {
        StringBuilder sb = new StringBuilder();
        for(String e : errors) {
            sb.append(e);
        }
        return sb.toString();
    }
    public String printAllTraces() {
        StringBuilder sb = new StringBuilder();
        for(String s : properties) {
            sb.append(printTrace(s));
        }
        return sb.toString();
    }

    public String printStatus() {
        StringBuilder sb = new StringBuilder();
        sb.append(proverStatus + "\n");
        if(errors.size() > 0) {
            for(String error : errors) {
                sb.append(error);
            }
        }
        return sb.toString();
    }
}
