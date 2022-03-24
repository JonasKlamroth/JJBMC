import java.util.*;
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

    public static class Trace {
        List<Assignment> assignments;
        Set<String> relevantVars = null;

        public Trace(List<Assignment> assignments) {
            this.assignments = assignments;
        }

        private void filterAssignments() {
            filterAssignments(relevantVars);
        }

        private boolean isRelevantVar(String var) {
            if(var == null) {
                return false;
            }
            for(String s : relevantVars) {
                if(s.equals(var)) {
                    return true;
                }
                if(var.equals("this." + s)) {
                    return true;
                }
            }
            if(var.contains("[")) {
                return isRelevantVar(var.substring(0, var.lastIndexOf("[")));
            }
            return false;
        }

        private void filterAssignments(Set<String> relevantVars) {
            List<Assignment> trace = assignments;
            if(relevantVars != null) {
                trace = trace.stream().filter(a -> isRelevantVar(a.guess)).collect(Collectors.toList());
            }
            trace = trace.stream().filter(a -> !a.jbmcVarname.equals("this")).collect(Collectors.toList());
            trace = trace.stream().filter(a -> !a.jbmcVarname.contains("malloc")).collect(Collectors.toList());
            List<Assignment> res = new ArrayList<>();
            int idx = 0;
            List<Assignment> group;
            while (idx < trace.size()) {
                group = new ArrayList<>();
                group.add(trace.get(idx));
                for (int i = idx; i < trace.size() - 1 && trace.get(i).lineNumber == trace.get(i + 1).lineNumber; ++i) {
                    idx = i + 1;
                    group.add(trace.get(i + 1));
                }
                idx++;
                res.addAll(filterGroup(group));
            }
            assignments = res;
        }

        private List<Assignment> filterGroup(List<Assignment> group) {
            LinkedHashMap<String, Assignment> groupMap = new LinkedHashMap<>();
            for(Assignment a : group) {
                groupMap.put(a.guess, a);
            }
            return new ArrayList<>(groupMap.values());
        }
    }

    public void addProperty(String name, Trace trace, int lineNumber, String reason, String ass) {
        properties.add(name);
        traces.add(trace);
        lineNumbers.add(lineNumber);
        reasons.add(reason);
        asserts.add(ass);
    }

    public static class Assignment {
        public String parameterName;
        public int lineNumber;
        protected String jbmcVarname;
        public String value;
        public String guess;

        public Assignment(int line, String jbmcVarname, String value, String guess, String parameterName) {
            this.parameterName = parameterName;
            this.lineNumber = line;
            this.setJbmcVarname(jbmcVarname);
            this.value = value;
            this.guess = guess;
        }

        @Override
        public String toString() {
            return "in line " + lineNumber + ": " + this.guess + " (" + jbmcVarname + ") = " + value;
        }

        public String getJbmcVarname() {
            return jbmcVarname;
        }

        public void setJbmcVarname(String jbmcVarname) {
            this.jbmcVarname = jbmcVarname;
        }
    }


    public String printTrace(String property, boolean printGuesses) {
        StringBuilder sb = new StringBuilder();
        int idx = properties.indexOf(property);
        if(idx == -1) {
            return "";
        }
        Trace trace = traces.get(idx);
        if(trace == null) {
            return "";
        }

        sb.append("Trace for PVC: " + property + " in line " + lineNumbers.get(idx) + "\n");
        trace.filterAssignments();
        if(printGuesses) {
            for (Assignment a : trace.assignments) {
                if(a.guess != null) {
                    sb.append(a + "\n");
                }
            }
        }
        if(asserts.get(idx) != null) {
            sb.append("Fail in line " + lineNumbers.get(idx) + ": " + asserts.get(idx) + " (" + reasons.get(idx) + ")\n");
        } else {
            sb.append("Fail in line " + lineNumbers.get(idx) + ": " + reasons.get(idx) + "\n");
        }
        sb.append("\n");
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
