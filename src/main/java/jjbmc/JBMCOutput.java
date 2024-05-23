package jjbmc;

import jjbmc.trace.Trace;
import jjbmc.trace.TraceInformation;
import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.NoArgsConstructor;
import lombok.Setter;
import org.jspecify.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

@Getter
@AllArgsConstructor
@NoArgsConstructor
public class JBMCOutput {
    @Setter private String proverStatus = "";
    private List<String> messages = new ArrayList<>();
    private List<String> errors = new ArrayList<>();
    private List<String> properties = new ArrayList<>();
    private List<@Nullable String> reasons = new ArrayList<>();
    private List<@Nullable String> asserts = new ArrayList<>();
    private List<@Nullable Trace> traces = new ArrayList<>();
    private List<Integer> lineNumbers = new ArrayList<>();

    public void addProperty(String name, @Nullable Trace trace, int lineNumber, @Nullable String reason, @Nullable String ass) {
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

        sb.append("Trace for PVC: ").append(property).append(" in line ").append(lineNumbers.get(idx)).append("\n");
        trace.filterAssignments();
        trace.getFinalVals();
        if (printGuesses) {
            for (Assignment a : trace.getFilteredAssignments()) {
                if (a.getGuess() != null) {
                    sb.append(a).append("\n");
                }
            }
        }
        if (asserts.get(idx) != null) {
            String assertion = asserts.get(idx);
            if (assertion != null && assertion.contains("\"Illegal assignment ")) {
                assertion = assertion.substring(assertion.indexOf("\"") + 1, assertion.length() - 2);
            }
            sb.append("Fail in line ").append(lineNumbers.get(idx)).append(": ").append(assertion).append(" (").append(reasons.get(idx)).append(")\n");
            sb.append("with concrete values: \n");
            sb.append(printFinalVals(traces.get(idx)));
        } else {
            sb.append("Fail in line ").append(lineNumbers.get(idx)).append(": ").append(reasons.get(idx)).append("\n");
        }
        sb.append("\n");
        return sb.toString();
    }

    private String printFinalVals(@Nullable Trace trace) {
        if (trace == null) return "";

        StringBuilder sb = new StringBuilder();
        for (String k : trace.finalVals.keySet()) {
            sb.append(TraceInformation.applyExpressionMap(k)).append(" = ").append(trace.finalVals.get(k));
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
        sb.append(proverStatus).append("\n");
        if (!errors.isEmpty()) {
            for (String error : errors) {
                sb.append(error);
            }
        }
        return sb.toString();
    }


    private String cutArrayString(String s, int size) {
        int pos = s.indexOf(",");
        while (--size > 0 && pos != -1) {
            pos = s.indexOf(",", pos + 1);
        }
        return s.substring(0, pos - 1) + "}";
    }


}
