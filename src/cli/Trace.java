package cli;

import static cli.TraceInformation.cleanLHS;
import static cli.TraceInformation.cleanValue;
import static cli.TraceInformation.isRelevantValue;

import java.util.ArrayList;
import java.util.Arrays;
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
    Set<String> relevantVars = new HashSet<>();
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
        if (var.startsWith("(") && var.endsWith(")")) {
            return false;
        }
        if (var.contains("@")) {
            return false;
        }
        for (String s : relevantVars) {
            String[] vars = var.split("=");
            for (String v : vars) {
                s = s.replace("this.", "").trim();
                v = v.replace("this.", "").trim();
                if (s.equals(v) || v.startsWith(v + ".")) {
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
        trace = trace.stream().filter(a -> !a.jbmcVarname.contains("this$0")).collect(Collectors.toList());
        trace = trace.stream().filter(a -> !a.jbmcVarname.contains("derefd_pointer")).collect(Collectors.toList());
        //trace = trace.stream().filter(a -> !a.value.contains("@class_identifier") && !a.value.startsWith("[")).collect(Collectors.toList());
        allAssignments = trace;
        List<Assignment> res = new ArrayList<>();
        int idx = 0;
        List<Assignment> group;
        while (idx < trace.size()) {
            group = new ArrayList<>();
            group.add(trace.get(idx));
            int newIdx = idx;
            for (int i = idx; i < trace.size() - 1 &&
                !TraceInformation.isActualNewLine(trace.get(idx).lineNumber, trace.get(i + 1).lineNumber); ++i) {
                newIdx = i + 1;
                group.add(trace.get(i + 1));
            }
            idx = newIdx;
            provideGuesses(group);
            group = filterGroup(group);
            for (int i = 0; i < group.size(); ++i) {
                group.get(i).guessedValue = getValue(group.get(i).value, idx);
                if ((group.get(i).jbmcVarname.contains("_object") || group.get(i).jbmcVarname.contains("_array")) &&
                        group.get(i).jbmcVarname.startsWith("dynamic_")) {
                    if (group.get(i).jbmcVarname.contains("[")) {
                        Object o = getValue(group.get(i).jbmcVarname.substring(0, group.get(i).jbmcVarname.indexOf("[")), idx);
                        group.get(i).guessedValue = o;
                        group.get(i).guess = group.get(i).guess.substring(0, group.get(i).guess.indexOf("["));
                    } else {
                        Object o = getValue(group.get(i).jbmcVarname, idx);
                        group.get(i).guessedValue = o;
                    }
                }
            }
            group = filterGroup(group);
            idx++;
            res.addAll(group);
        }


        if (relevantVars != null || CLI.fullTraceRequested) {
            res = res.stream().filter(a -> isRelevantVar(a.guess)).collect(Collectors.toList());
        }
        return res;
    }

    private Object getValue(String value, int idx) {
        value = value.trim();
        value = cleanValue(value);
        if (value.contains("#")) {
            //not sure if this is always correct
            return new ArrayList<>(Arrays.asList(new Object[CLI.maxArraySize]));
        }
        if (value.equals("null")) {
            return "null";
        }
        try {
            int val = Integer.parseInt(value);
            return val;
        } catch (NumberFormatException e) {
            //this may happen
        }
        try {
            float val = Float.parseFloat(value);
            return val;
        } catch (NumberFormatException e) {
            //this may happen
        }
        try {
            long val = Long.parseLong(value);
            return val;
        } catch (NumberFormatException e) {
            //this may happen
        }
        try {
            double val = Double.parseDouble(value);
            return val;
        } catch (NumberFormatException e) {
            //this may happen
        }
        if (value.equals("true")) {
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
            value = value.replace("{", "");
            value = value.substring(0, value.length() - 1);
            String[] values = value.split(",");
            if (!values[0].trim().startsWith(".@")) {
                //its an array
                List<Object> vals = new ArrayList<>();
                for (String val : values) {
                    vals.add(getValue(val, idx));
                }
                return vals;
            } else {
                //its an object
                Map<String, Object> vals = new HashMap<>();
                for (String val : values) {
                    val = val.trim();
                    String key = val.substring(0, val.indexOf("=")).trim();
                    key = key.replace(".", "");
                    String innerVal = val.substring(val.indexOf("=") + 1).trim();

                    if (!key.startsWith("@") && !key.contains("this$0")) {
                        vals.put(key, getValue(innerVal, idx));
                    }
                }
                return vals;
            }
        }
        //guess its a String
        return value;
    }

    private Object findValue(String value) {
        return findValue(value, allAssignments.size() - 1);

    }

    private List<Assignment> filterGroup(List<Assignment> group) {
        //group = group.stream().filter(a -> !a.value.contains("dynamic_object")).collect(Collectors.toList());
        LinkedHashMap<String, Assignment> groupMap = new LinkedHashMap<>();
        for (Assignment a : group) {
            groupMap.put(a.guess, a);
        }
        if (groupMap.containsKey(null)) {
            groupMap.remove(null);
        }
        List<Assignment> filtered = new ArrayList<>(groupMap.values());
        return filtered;
    }

    private Object findValue(String value, int maxIdx) {
        //all assignments in the same lane will be respected
        while (maxIdx < allAssignments.size() - 1 && allAssignments.get(maxIdx).lineNumber == allAssignments.get(maxIdx + 1).lineNumber) {
            maxIdx++;
        }
        value = value.replace("&", "");
        for (int i = maxIdx; i >= 0; --i) {
            if (allAssignments.get(i).jbmcVarname.equals(value) || allAssignments.get(i).jbmcVarname.equals(value + ".data")) {
                Object val = getValue(allAssignments.get(i).value, maxIdx);
                if (val instanceof ArrayList) {
                    val = performArrayUpdates(allAssignments.get(i).jbmcVarname, val, i, maxIdx);
                }
                if (val instanceof Map) {
                    val = performFieldUpdates(allAssignments.get(i).jbmcVarname, val, i, maxIdx);
                }
                return val;
            }
        }
        if (value.startsWith("dynamic_object")) {
            return performFieldUpdates(value, new HashMap<String, Object>(), 0, maxIdx);
        }
        return noValue;
    }

    private Object performArrayUpdates(String varName, Object val, int idx, int maxIdx) {
        @SuppressWarnings("unchecked") ArrayList<Object> valArray = (ArrayList<Object>) val;
        for (int i = idx; i < maxIdx; ++i) {
            if (allAssignments.get(i).jbmcVarname.startsWith(varName + "[")) {
                try {
                    String s = allAssignments.get(i).jbmcVarname;
                    s = s.replace("L]", "]");
                    s = s.substring(s.indexOf("[") + 1, s.indexOf("]"));
                    int index = Integer.parseInt(s);
                    if (index >= valArray.size()) {
                        System.out.println("error updating array in trace.");
                    } else {
                        valArray.set(index, getValue(allAssignments.get(i).value, maxIdx));
                    }

                } catch (NumberFormatException e) {
                    throw new RuntimeException("Error parsing the trace.");
                }
            }
        }
        return valArray;
    }

    private Object performFieldUpdates(String varName, Object val, int idx, int maxIdx) {
        @SuppressWarnings("unchecked") Map<String, Object> valMap = (Map<String, Object>) val;
        for (int i = idx; i < maxIdx; ++i) {
            if (allAssignments.get(i).jbmcVarname.startsWith(varName + ".")) {
                String s = allAssignments.get(i).jbmcVarname;
                String fieldName = s.substring(s.indexOf(".") + 1);
                if (!fieldName.startsWith("@") && !fieldName.contains("this$")) {
                    valMap.put(fieldName, getValue(allAssignments.get(i).value));
                }
            }
        }
        return valMap;
    }

    void getFinalVals() {
        for (String rv : relevantVars) {
            for (Assignment a : this.filteredAssignments) {
                String[] vars = a.guess.split("=");
                for (String v : vars) {
                    v = v.trim().replace("this.", "");
                    rv = rv.trim().replace("this.", "");
                    if (v.equals(rv)) {
                        finalVals.put(rv, a.guessedValue.toString());
                    }
                }
            }
        }
    }

    private Object getValue(String value) {
        return getValue(value, allAssignments.size() - 1);
    }

    public void provideGuesses(List<Assignment> lineAssignments) {
        for (int i = 0; i < lineAssignments.size(); ++i) {
            Assignment a = lineAssignments.get(i);
            a.value = cleanValue(a.value);
            a.jbmcVarname = cleanLHS(a.jbmcVarname);
            if (isRelevantValue(a.value)) {
                if (a.value.startsWith("dynamic_")) {
                    String value = cleanValue(a.value);
                    trackDynamicObject(a.jbmcVarname, value);
                }
                if (a.jbmcVarname.endsWith(".data") && a.value.contains("dynamic_") && a.value.contains("_array")) {
                    String value = cleanValue(a.value);
                    trackDynamicObject(a.jbmcVarname.substring(0, a.jbmcVarname.length() - 5), value);
                }
            }
        }
        for (int i = 0; i < lineAssignments.size(); ++i) {
            Assignment a = lineAssignments.get(i);
            if (a.jbmcVarname.startsWith("array_data_init")) {
                processArrayInit(lineAssignments, i);
            }
            if (isRelevantValue(a.value)) {
                a.guess = guessVariable(a.jbmcVarname);
                if (a.guess != null && a.parameterName != null) {
                    String method = TraceInformation.getMethod(TraceInformation.getStartingLineForMethodAt(a.lineNumber));
                    if (a.parameterName.contains(method)) {
                        if (!a.guess.isEmpty()) {
                            relevantVars.add(a.guess);
                        }
                    }
                }
            }
            a.lineNumber = TraceInformation.getOriginalLine(a.lineNumber);
        }
    }

    private void processArrayInit(List<Assignment> lineAssignments, int idx) {
        int arrayIdx = 0;
        String arrayName = lineAssignments.get(idx).value;
        int length = findArrayLength(arrayName, idx, lineAssignments);
        if (length <= 0) {
            return;
        }
        for (int i = idx; true; ++i) {
            Assignment a = lineAssignments.get(i);
            if (a.jbmcVarname.startsWith("new_array_item")) {
                a.jbmcVarname = arrayName + "[" + arrayIdx + "]";
            }
            if (a.jbmcVarname.startsWith("array_init_iter")) {
                int newIdx = -1;
                try {
                    newIdx = Integer.parseInt(a.value);
                } catch (Exception e) {
                    System.out.println("Error parsing trace.");
                }
                if (newIdx == length) {
                    break;
                } else {
                    arrayIdx = newIdx;
                }
            }
        }
    }

    private int findArrayLength(String arrayName, int startIdx, List<Assignment> assignments) {
        while (startIdx < assignments.size() - 1 && assignments.get(startIdx).lineNumber == assignments.get(startIdx + 1).lineNumber) {
            startIdx++;
        }
        while (arrayName.contains("array")) {
            arrayName = objectMap.get(arrayName);
            if (arrayName == null) {
                return -1;
            }
        }
        for (int i = startIdx; 0 <= i; --i) {
            if (assignments.get(i).jbmcVarname.equals(arrayName + ".length")) {
                return Integer.parseInt(assignments.get(i).value);
            }
        }
        return -1;
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
            if (object == null && !lhs.contains("[")) {
                return lhs;
            } else if (object != null) {
                String res = lhs.replace(lhs.substring(0, lhs.indexOf(".")), object);
                if (res.endsWith(".data")) {
                    return res.substring(0, res.length() - 5);
                }
                return res;
            }
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
        if (object != null) {
            return applyObjectMap(object);
        }
        return lhs;
    }

    public String guessVariable(String lhs) {
        return guessVariable(lhs, false);
    }

    public String guessVariable(String lhs, boolean getAll) {
        if (lhs == null) {
            return null;
        }

        String res = applyObjectMap(lhs);
        String oldRes = null;
        while (!res.equals(oldRes)) {
            oldRes = res;
            res = applyObjectMap(res);
        }

        String tmpRes = res;
        String rest = "";
        if (tmpRes.contains("[")) {
            rest = tmpRes.substring(tmpRes.indexOf("["));
            tmpRes = tmpRes.substring(0, tmpRes.indexOf("["));
        }
        String object = reverseObjectMap.get(tmpRes);
        if (object != null) {
            res = "";
            for (Map.Entry<String, String> k : reverseObjectMap.entrySet()) {
                if (k.getValue().equals(object) &&
                        (relevantVars.contains(k.getKey()) || relevantVars.stream().anyMatch(s -> k.getKey().endsWith("." + s))) || getAll) {
                    res += k.getKey() + " = ";
                }
            }
            if (!res.isEmpty()) {
                tmpRes = res.substring(0, res.length() - 3);
                if(tmpRes.contains(".")) {
                    String[] s = tmpRes.split("\\.");
                    String r = applyObjectMap(s[0]);
                    String oldR = null;
                    while (!r.equals(oldR)) {
                        oldR = r;
                        r = applyObjectMap(r);
                    }
                    if(r != null) {
                        tmpRes = r + "." + s[1];
                    }
                }
            } else {
                return null;
            }
        }
        return tmpRes + rest;
    }



}

