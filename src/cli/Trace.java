package cli;

import static cli.TraceInformation.cleanValue;
import static cli.TraceInformation.isRelevantValue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public class Trace {
    private Object noValue = new Object();
    List<Assignment> filteredAssignments;
    List<Assignment> allAssignments;
    Set<String> relevantVars = null;
    private final Map<String, String> objectMap = new HashMap<>();
    private final Map<String, String> reverseObjectMap = new HashMap<>();

    Map<String, Object> finalVals = new HashMap<String, Object>();

    public Trace(List<Assignment> assignments) {
        this.allAssignments = assignments;
    }

    public void filterAssignments() {
        relevantVars.addAll(CLI.relevantVars);
        filteredAssignments = filterAssignments(relevantVars);
    }

    private boolean isRelevantVar(String var) {
        if (var == null) {
            return false;
        }
        if(var.startsWith("(") && var.endsWith(")")) {
            return false;
        }
        for (String s : relevantVars) {
            String[] vars = var.split("=");
            for(String v : vars) {
                s = s.replace("this.", "");
                v = v.replace("this.", "");
                if (s.equals(v.trim())) {
                    return true;
                }
            }
        }
        if (var.contains("[")) {
            return isRelevantVar(var.substring(0, var.lastIndexOf("[")));
        }
        return false;
    }

    private List<Assignment> filterAssignments(Set<String> relevantVars) {
        List<Assignment> trace = allAssignments;
        //trace = trace.stream().filter(a -> !a.jbmcVarname.equals("this")).collect(Collectors.toList());
        trace = trace.stream().filter(a -> !a.jbmcVarname.contains("malloc")).collect(Collectors.toList());
        trace = trace.stream().filter(a -> !a.jbmcVarname.contains("derefd_pointer")).collect(Collectors.toList());
        trace = trace.stream().filter(a -> !a.value.contains("@class_identifier")).collect(Collectors.toList());
        allAssignments = trace;
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
            provideGuesses(group);
            group = filterGroup(group);
            for(int i = 0; i < group.size(); ++i) {
                if (i + 2  + CLI.maxArraySize < group.size() && group.get(i + 1).jbmcVarname.endsWith(".length") && group.get(i + 2).jbmcVarname.endsWith(".data")) {
                    //this is a combined array assignment
                    group.get(i).value = getValue(group.get(i).value, idx).toString();

                    for(int j = 0; j < CLI.maxArraySize + 2; ++j) {
                        group.remove(i + 1);
                    }
                } else {
                    group.get(i).value = getValue(group.get(i).value, idx).toString();
                }
            }
            idx++;
            res.addAll(group);
        }


        if (relevantVars != null || CLI.fullTraceRequested) {
            res = res.stream().filter(a -> isRelevantVar(a.guess)).collect(Collectors.toList());
        }
        return res;
    }

    private Object getValue(String value, int idx) {
        if(value.equals("null")) {
            return "null";
        }
        try {
            int val = Integer.parseInt(value);
            return val;
        } catch (NumberFormatException _) {
            //this may happen
        }
        try {
            float val = Float.parseFloat(value);
            return val;
        } catch (NumberFormatException _) {
            //this may happen
        }
        try {
            long val = Long.parseLong(value);
            return val;
        } catch (NumberFormatException _) {
            //this may happen
        }
        try {
            double val = Double.parseDouble(value);
            return val;
        } catch (NumberFormatException _) {
            //this may happen
        }
        if(value.equals("true")) {
            return true;
        }
        if (value.equals("false")) {
            return false;
        }
        if (value.startsWith("&dynamic") || value.startsWith("dynamic_")) {
            return findValue(value, idx);
        }
        if (value.startsWith("{")) {
            //its an array
            value = value.replace("{", "").replace("}", "");
            String[] values = value.split(",");
            List<Object> vals = new ArrayList<>();
            for(String val : values) {
                vals.add(getValue(val, idx));
            }
            return vals;
        }
        //guess its a String
        return value;
    }

    private Object findValue(String value) {
        return findValue(value, allAssignments.size() - 1);

    }

    private List<Assignment> filterGroup(List<Assignment> group) {
        LinkedHashMap<String, Assignment> groupMap = new LinkedHashMap<>();
        for (Assignment a : group) {
            groupMap.put(a.guess, a);
        }
        List<Assignment> filtered = new ArrayList<>(groupMap.values());
        return filtered;
    }

    private Object findValue(String value, int maxIdx) {
        value = value.replace("&", "");
        for(int i = maxIdx; i >= 0; --i) {
            if (allAssignments.get(i).jbmcVarname.equals(value) || allAssignments.get(i).jbmcVarname.equals(value + ".data")) {
                Object val = getValue(allAssignments.get(i).value, maxIdx);
                if(val instanceof ArrayList) {
                    val = performArrayUpdates(allAssignments.get(i), val, i, maxIdx);
                }
                return val;
            }
        }
        return noValue;
    }

    private Object performArrayUpdates(Assignment assignment, Object val, int idx, int maxIdx) {
        ArrayList valArray = (ArrayList)val;
        String varName = assignment.jbmcVarname;
        for(int i = idx; i < maxIdx; ++i) {
            if(allAssignments.get(i).jbmcVarname.startsWith(varName + "[")) {
                try {
                    String s = allAssignments.get(i).jbmcVarname;
                    int index = Integer.parseInt(s.substring(s.indexOf("[") + 1, s.indexOf("]") - 1));
                    valArray.set(index, getValue(allAssignments.get(i).value));

                } catch (NumberFormatException e) {}
            }
        }
        return valArray;
    }

    void getFinalVals() {
        for(String rv : relevantVars) {
            for(Assignment a : this.filteredAssignments) {
                String[] vars = a.guess.split("=");
                for(String v : vars) {
                    if (v.trim().equals(rv)) {
                        finalVals.put(rv, getValue(a.value));
                    }
                }
            }
        }
    }

    private Object getValue(String value) {
        return getValue(value, allAssignments.size() - 1);
    }

    public void provideGuesses(List<Assignment> lineAssignments) {
        String t = null;
        for (int i = 0; i < lineAssignments.size(); ++i) {
            Assignment a = lineAssignments.get(i);
            if (isRelevantValue(a.value)) {
                if (a.value.startsWith("&dynamic_") || a.value.startsWith("dynamic")) {
                    String value = cleanValue(a.value);
                    trackDynamicObject(a.jbmcVarname, value);
                }
                if (a.jbmcVarname.endsWith(".data") && a.value.contains("dynamic_") && a.value.contains("_array")) {
                    String guess = guessVariable(a.jbmcVarname);
                    String value = cleanValue(a.value);
                    if (guess != null) {
                        trackDynamicObject(guess, value);
                    } else {
                        trackDynamicObject(a.jbmcVarname, value);
                    }
                }
            }
        }
        for (int i = lineAssignments.size() - 1; i >= 0; --i) {
            Assignment a = lineAssignments.get(i);
            if (isRelevantValue(a.value)) {
                a.guess = guessVariable(a.jbmcVarname);
                if (a.guess != null && a.parameterName != null) {
                    String method = TraceInformation.getMethod(TraceInformation.getStartingLineForMethodAt(a.lineNumber));
                    if (a.parameterName.contains(method)) {
                        if(!a.guess.isEmpty()) {
                            relevantVars.add(a.guess);
                        }
                    }
                }
            }
            a.lineNumber = TraceInformation.getOriginalLine(a.lineNumber);
        }
    }

    private void trackDynamicObject(String jbmcVarname, String value) {
        if (!jbmcVarname.contains("array_data")) {
            objectMap.put(value, jbmcVarname);
        }
        reverseObjectMap.put(jbmcVarname, value);
    }

    private String getObjectName(String object) {
        if (object == null) {
            return null;
        }
        return objectMap.get(object);
    }

    private String applyObjectMap(String lhs) {
        if (lhs.contains(".")) {
            String object = getObjectName(lhs.substring(0, lhs.indexOf(".")));
            if (object == null) {
                return lhs;
            }
            String res = lhs.replace(lhs.substring(0, lhs.indexOf(".")), object);
            if(res.endsWith(".data")) {
                return res.substring(0, res.length() - 5);
            }
            return res;
        }
        if (lhs.contains("[")) {
            String object = getObjectName(lhs.substring(0, lhs.indexOf("[")));
            if (object == null) {
                return lhs;
            }
            if (object.endsWith(".data")) {
                return lhs.replace(lhs.substring(0, lhs.indexOf("[")), object.substring(0, object.length() - 5));
            }
            return lhs.replace(lhs.substring(0, lhs.indexOf("[")), object);

        }
        String object = getObjectName(lhs);
        if(object != null) {
            return applyObjectMap(object);
        }
        return lhs;
    }

    public String guessVariable(String lhs) {
        if (lhs == null) {
            return null;
        }
        for (String s : TraceInformation.ignoredVars) {
            if (lhs.contains(s)) {
                return null;
            }
        }
        String res = applyObjectMap(lhs);
        String oldRes = null;
        while (!res.equals(oldRes)) {
            oldRes = res;
            res = applyObjectMap(res);
        }

        for (String s : TraceInformation.ignoredVars) {
            if (res.contains(s)) {
                return null;
            }
        }
        //res = TraceInformation.applyExpressionMap(res);
        String tmpRes = res;
        String rest = "";
        if(tmpRes.contains("[")) {
            rest = tmpRes.substring(tmpRes.indexOf("["));
            tmpRes = tmpRes.substring(0, tmpRes.indexOf("["));
        }
        String object = reverseObjectMap.get(tmpRes);
        if(object != null) {
            res = "";
            for (Map.Entry<String, String> k : reverseObjectMap.entrySet()) {
                if (k.getValue().equals(object) && relevantVars.contains(k.getKey())) {
                    res += k.getKey() + " = ";
                }
            }
            if(!res.isEmpty()) {
                res = res.substring(0, res.length() - 3);
            }
        }
        return res + rest;
    }



}

