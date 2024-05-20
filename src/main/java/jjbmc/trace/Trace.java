package jjbmc.trace;

import jjbmc.Assignment;
import lombok.Getter;
import lombok.Setter;
import org.jspecify.annotations.Nullable;

import java.util.*;

import static jjbmc.trace.TraceInformation.*;

@Getter
public class Trace {
    private static final Object noValue = new Object();
    private final List<Assignment> filteredAssignments = new LinkedList<>();
    private List<Assignment> allAssignments = new LinkedList<>();
    @Setter private Set<String> relevantVars = new HashSet<>();
    private final Map<String, String> objectMap = new HashMap<>();
    private final Map<String, String> reverseObjectMap = new HashMap<>();
    public Map<String, Object> finalVals = new HashMap<>();

    private final boolean fullTraceRequested;
    private final int maxArraySize;

    public Trace(List<Assignment> assignments) {
        this(assignments, false, 10);
    }

    public Trace(List<Assignment> assignments, boolean fullTraceRequested, int maxArraySize) {
        this.allAssignments = assignments;
        this.fullTraceRequested = fullTraceRequested;
        this.maxArraySize = maxArraySize;
    }

    private boolean isRelevantVar(@Nullable String var) {
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

    public void filterAssignments() {
        List<Assignment> trace = allAssignments.stream()
                //trace = trace.stream().filter(a -> !a.jbmcVarname.equals("this")).collect(Collectors.toList());
                .filter(a -> !a.getJbmcVarname().contains("malloc"))
                .filter(a -> !a.getJbmcVarname().contains("this$0"))
                .filter(a -> !a.getJbmcVarname().contains("derefd_pointer"))
                .toList();
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
                    !TraceInformation.isActualNewLine(trace.get(idx).getLineNumber(), trace.get(i + 1).getLineNumber()); ++i) {
                newIdx = i + 1;
                group.add(trace.get(i + 1));
            }
            idx = newIdx;
            provideGuesses(group);
            group = filterGroup(group);
            for (Assignment assignment : group) {
                assignment.setGuessedValue(getValue(assignment.getValue(), idx));
                if ((assignment.getJbmcVarname().contains("_object") || assignment.getJbmcVarname().contains("_array")) &&
                        assignment.getJbmcVarname().startsWith("dynamic_")) {
                    if (assignment.getJbmcVarname().contains("[")) {
                        assignment.setGuessedValue(getValue(assignment.getJbmcVarname().substring(0, assignment.getJbmcVarname().indexOf("[")), idx));
                        assignment.setGuess(assignment.getGuess().substring(0, assignment.getGuess().indexOf("[")));
                    } else {
                        assignment.setGuessedValue(getValue(assignment.getJbmcVarname(), idx));
                    }
                }
            }
            group = filterGroup(group);
            idx++;
            res.addAll(group);
        }


        if (fullTraceRequested) {
            res = res.stream().filter(a -> isRelevantVar(a.getGuess())).toList();
        }
    }

    private Object getValue(String value, int idx) {
        value = value.trim();
        value = cleanValue(value);
        if (value.contains("#")) {
            //not sure if this is always correct
            return new ArrayList<>(Arrays.asList(new Object[maxArraySize]));
        }
        if (value.equals("null")) {
            return "null";
        }
        try {
            return Integer.parseInt(value);
        } catch (NumberFormatException e) {
            //this may happen
        }
        try {
            return Float.parseFloat(value);
        } catch (NumberFormatException e) {
            //this may happen
        }
        try {
            return Long.parseLong(value);
        } catch (NumberFormatException e) {
            //this may happen
        }
        try {
            return Double.parseDouble(value);
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
            groupMap.put(a.getGuess(), a);
        }
        groupMap.remove(null);
        return new ArrayList<>(groupMap.values());
    }

    private Object findValue(String value, int maxIdx) {
        //all assignments in the same lane will be respected
        while (maxIdx < allAssignments.size() - 1 && allAssignments.get(maxIdx).getLineNumber() == allAssignments.get(maxIdx + 1).getLineNumber()) {
            maxIdx++;
        }
        value = value.replace("&", "");
        for (int i = maxIdx; i >= 0; --i) {
            if (allAssignments.get(i).getJbmcVarname().equals(value) || allAssignments.get(i).getJbmcVarname().equals(value + ".data")) {
                Object val = getValue(allAssignments.get(i).getValue(), maxIdx);
                if (val instanceof ArrayList) {
                    val = performArrayUpdates(allAssignments.get(i).getJbmcVarname(), val, i, maxIdx);
                }
                if (val instanceof Map) {
                    val = performFieldUpdates(allAssignments.get(i).getJbmcVarname(), val, i, maxIdx);
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
            if (allAssignments.get(i).getJbmcVarname().startsWith(varName + "[")) {
                try {
                    String s = allAssignments.get(i).getJbmcVarname();
                    s = s.replace("L]", "]");
                    s = s.substring(s.indexOf("[") + 1, s.indexOf("]"));
                    int index = Integer.parseInt(s);
                    if (index >= valArray.size()) {
                        System.out.println("error updating array in trace.");
                    } else {
                        valArray.set(index, getValue(allAssignments.get(i).getValue(), maxIdx));
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
            if (allAssignments.get(i).getJbmcVarname().startsWith(varName + ".")) {
                String s = allAssignments.get(i).getJbmcVarname();
                String fieldName = s.substring(s.indexOf(".") + 1);
                if (!fieldName.startsWith("@") && !fieldName.contains("this$")) {
                    valMap.put(fieldName, getValue(allAssignments.get(i).getValue()));
                }
            }
        }
        return valMap;
    }

    public void getFinalVals() {
        for (String rv : relevantVars) {
            for (Assignment a : this.filteredAssignments) {
                String[] vars = a.getGuess().split("=");
                for (String v : vars) {
                    v = v.trim().replace("this.", "");
                    rv = rv.trim().replace("this.", "");
                    if (v.equals(rv)) {
                        finalVals.put(rv, a.getGuessedValue().toString());
                    }
                }
            }
        }
    }

    private Object getValue(String value) {
        return getValue(value, allAssignments.size() - 1);
    }

    public void provideGuesses(List<Assignment> lineAssignments) {
        for (Assignment a : lineAssignments) {
            a.setValue(cleanValue(a.getValue()));
            a.setJbmcVarname(cleanLHS(a.getJbmcVarname()));
            if (isRelevantValue(a.getValue())) {
                if (a.getValue().startsWith("dynamic_")) {
                    String value = cleanValue(a.getValue());
                    trackDynamicObject(a.getJbmcVarname(), value);
                }
                if (a.getJbmcVarname().endsWith(".data") && a.getValue().contains("dynamic_") && a.getValue().contains("_array")) {
                    String value = cleanValue(a.getValue());
                    trackDynamicObject(a.getJbmcVarname().substring(0, a.getJbmcVarname().length() - 5), value);
                }
            }
        }
        for (int i = 0; i < lineAssignments.size(); ++i) {
            Assignment a = lineAssignments.get(i);
            if (a.getJbmcVarname().startsWith("array_data_init")) {
                processArrayInit(lineAssignments, i);
            }
            if (isRelevantValue(a.getValue())) {
                a.setGuess(guessVariable(a.getJbmcVarname()));
                if (a.getGuess() != null && a.getParameterName() != null) {
                    String method = TraceInformation.getMethod(TraceInformation.getStartingLineForMethodAt(a.getLineNumber()));
                    if (a.getParameterName().contains(method)) {
                        if (!a.getGuess().isEmpty()) {
                            relevantVars.add(a.getGuess());
                        }
                    }
                }
            }
            a.setLineNumber(TraceInformation.getOriginalLine(a.getLineNumber()));
        }
    }

    private void processArrayInit(List<Assignment> lineAssignments, int idx) {
        int arrayIdx = 0;
        String arrayName = lineAssignments.get(idx).getValue();
        int length = findArrayLength(arrayName, idx, lineAssignments);
        if (length <= 0) {
            return;
        }
        for (int i = idx; true; ++i) {
            Assignment a = lineAssignments.get(i);
            if (a.getJbmcVarname().startsWith("new_array_item")) {
                a.setJbmcVarname(arrayName + "[" + arrayIdx + "]");
            }
            if (a.getJbmcVarname().startsWith("array_init_iter")) {
                int newIdx = -1;
                try {
                    newIdx = Integer.parseInt(a.getValue());
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
        while (startIdx < assignments.size() - 1 && assignments.get(startIdx).getLineNumber() == assignments.get(startIdx + 1).getLineNumber()) {
            startIdx++;
        }
        while (arrayName.contains("array")) {
            arrayName = objectMap.get(arrayName);
            if (arrayName == null) {
                return -1;
            }
        }
        for (int i = startIdx; 0 <= i; --i) {
            if (assignments.get(i).getJbmcVarname().equals(arrayName + ".length")) {
                return Integer.parseInt(assignments.get(i).getValue());
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

    private @Nullable String getObjectName(@Nullable String object) {
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

    public @Nullable String guessVariable(@Nullable String lhs) {
        if (lhs == null) {
            return null;
        }

        StringBuilder res = new StringBuilder(applyObjectMap(lhs));
        String oldRes = null;
        while (!res.toString().equals(oldRes)) {
            oldRes = res.toString();
            res = new StringBuilder(applyObjectMap(res.toString()));
        }

        String tmpRes = res.toString();
        String rest = "";
        if (tmpRes.contains("[")) {
            rest = tmpRes.substring(tmpRes.indexOf("["));
            tmpRes = tmpRes.substring(0, tmpRes.indexOf("["));
        }
        String object = reverseObjectMap.get(tmpRes);
        if (object != null) {
            res = new StringBuilder();
            for (Map.Entry<String, String> k : reverseObjectMap.entrySet()) {
                if (k.getValue().equals(object) && relevantVars.contains(k.getKey())) {
                    res.append(k.getKey()).append(" = ");
                }
            }
            if (!res.isEmpty()) {
                tmpRes = res.substring(0, res.length() - 3);
            } else {
                return null;
            }
        }
        return tmpRes + rest;
    }
}

