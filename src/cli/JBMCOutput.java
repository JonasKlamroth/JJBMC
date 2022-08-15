package cli;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public class JBMCOutput {
    public String proverStatus = "";
    public List<String> messages = new ArrayList<>();
    public List<String> errors = new ArrayList<>();
    public List<String> properties = new ArrayList<>();
    public List<String> reasons = new ArrayList<>();
    public List<String> asserts = new ArrayList<>();
    public List<Trace> traces = new ArrayList<>();
    public List<Integer> lineNumbers = new ArrayList<>();

    public void addProperty(String name, Trace trace, int lineNumber, String reason, String ass) {
        properties.add(name);
        traces.add(trace);
        lineNumbers.add(lineNumber);
        reasons.add(reason);
        asserts.add(ass);
    }

    public String printTrace(String property, boolean printGuesses) {
        StringBuilder sb = new StringBuilder();
        int idx = properties.indexOf(property);
        if (idx == -1) {
            return "";
        }
        Trace trace = traces.get(idx);
        if (trace == null) {
            return "";
        }

        sb.append("Trace for PVC: " + property + " in line " + lineNumbers.get(idx) + "\n");
        trace.filterAssignments();
        trace.getFinalVals();
        if (printGuesses) {
            for (Assignment a : trace.filteredAssignments) {
                if (a.guess != null) {
                    sb.append(a + "\n");
                }
            }
        }
        if (asserts.get(idx) != null) {
            String assertion = asserts.get(idx);
            if (assertion.contains("\"Illegal assignment ")) {
                assertion = assertion.substring(assertion.indexOf("\"") + 1, assertion.length() - 2);
            }
            sb.append("Fail in line " + lineNumbers.get(idx) + ": " + assertion + " (" + reasons.get(idx) + ")\n");
            sb.append("with concrete values: " + "\n");
            sb.append(printFinalVals(traces.get(idx)));
        } else {
            sb.append("Fail in line " + lineNumbers.get(idx) + ": " + reasons.get(idx) + "\n");
        }
        sb.append("\n");
        return sb.toString();
    }

    private String printFinalVals(Trace trace) {
        StringBuilder sb = new StringBuilder();
        for(String k : trace.finalVals.keySet()) {
            sb.append(TraceInformation.applyExpressionMap(k) + " = " + trace.finalVals.get(k));
            sb.append("\n");
        }
        return sb.toString();
    }

    public String printTrace(String property) {
        return printTrace(property, true);
    }

    public String printErrors() {
        StringBuilder sb = new StringBuilder();
        for (String e : errors) {
            sb.append(e);
        }
        return sb.toString();
    }

    public String printAllTraces() {
        StringBuilder sb = new StringBuilder();
        for (String s : properties) {
            sb.append(printTrace(s));
        }
        return sb.toString();
    }

    public String printStatus() {
        StringBuilder sb = new StringBuilder();
        sb.append(proverStatus + "\n");
        if (errors.size() > 0) {
            for (String error : errors) {
                sb.append(error);
            }
        }
        return sb.toString();
    }


    private String cutArrayString(String s, int size) {
        int pos = s.indexOf(",");
        while (--size > 0 && pos != -1)
            pos = s.indexOf(",", pos + 1);
        return s.substring(0, pos - 1) + "}";
    }


}
