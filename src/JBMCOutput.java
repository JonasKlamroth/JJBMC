import java.util.*;
import java.util.stream.Collectors;

public class JBMCOutput {
    public String proverStatus = "";
    public List<String> messages = new ArrayList<>();
    public List<String> errors = new ArrayList<>();
    public List<String> properties = new ArrayList<>();
    public List<String> reasons = new ArrayList<>();
    public List<Trace> traces = new ArrayList<>();
    public List<Integer> lineNumbers = new ArrayList<>();
    public List<String> failingLines = new ArrayList<>();

    public static class Trace {
        List<Assignment> assignments;
        Set<Guess> guesses;

        public static class Guess {
            String varName;
            String idea = null;
            int lineNumber = 0;

            public Guess(String varName, String idea, int lineNumber) {
                this.varName = varName;
                this.idea = idea;
                this.lineNumber = lineNumber;
            }

            @Override
            public int hashCode() {
                return Objects.hash(varName, idea, lineNumber);
            }

            @Override
            public boolean equals(Object o) {
                if(!(o instanceof Guess)) {
                    return false;
                }
                Guess other = (Guess) o;
                return other.varName.equals(varName) && other.lineNumber == lineNumber && other.idea.equals(idea);
            }
        }

        public Trace(List<Assignment> assignments, Set<Guess> guesses) {
            this.assignments = assignments;
            this.guesses = guesses;
        }

        public void addGuess(String varName, String idea, int lineNumber) {
            guesses.add(new Guess(varName, idea, lineNumber));
        }

        public void applyGuesses() {
            for(int i = 0; i < assignments.size(); ++i) {
                String var = assignments.get(i).getJbmcVarname();
                int finalI = i;
                List<Guess> filteredGuesses = guesses.stream().filter(g -> g.lineNumber <= assignments.get(finalI).lineNumber).
                        sorted((Comparator.comparingInt(guess -> guess.lineNumber))).
                        collect(Collectors.toList());
                Collections.reverse(filteredGuesses);
                for(Guess g : filteredGuesses) {
                    var = var.replace(g.varName, g.idea);
                }
                assignments.get(i).setJbmcVarname(var);
            }
        }


        private void filterAssignments() {
            List<Assignment> trace = assignments;
            List<Assignment> res = new ArrayList<>();
            int idx = 0;
            List<Assignment> group = new ArrayList<>();
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
            res = res.stream().filter(a -> !a.jbmcVarname.equals("this")).collect(Collectors.toList());
            assignments = res;
        }

        private List<Assignment> filterGroup(List<Assignment> group) {
            LinkedHashMap<String, Assignment> groupMap = new LinkedHashMap<>();
            for(Assignment a : group) {
                groupMap.put(a.getJbmcVarname(), a);
            }
            List<Assignment> res = new ArrayList<>();
            res.addAll(groupMap.values());
            return res;
        }
    }

    public void addProperty(String name, Trace trace, int lineNumber, String failingLine, String reason) {
        properties.add(name);
        traces.add(trace);
        lineNumbers.add(lineNumber);
        failingLines.add(failingLine);
        reasons.add(reason);
    }

    public static class Assignment {
        public int lineNumber;
        protected String jbmcVarname;
        public String value;
        public String sourceLine;

        public Assignment(int line, String jbmcVarname, String value, String sourceLine) {
            this.lineNumber = line;
            this.setJbmcVarname(jbmcVarname);
            this.value = value;
            this.sourceLine = sourceLine;
        }

        public Assignment(String line, String jbmcVarname, String value, String sourceLine) {
            this(Integer.parseInt(line), jbmcVarname, value, sourceLine);
        }

        @Override
        public String toString() {
            return "in line " + lineNumber + ": " + getJbmcVarname() + " = " + value;
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
        trace.applyGuesses();
        trace.filterAssignments();
        if(printGuesses) {
            for (Assignment a : trace.assignments) {
                sb.append(a + "\n");
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
