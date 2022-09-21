package cli;

import static cli.TraceInformation.cleanLHS;
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
        allAssignments.get(0).toString();
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
                if(group.get(i).jbmcVarname.contains("_array") && group.get(i).jbmcVarname.startsWith("dynamic_")) {
                    if(group.get(i).jbmcVarname.contains("[")) {
                        Object o = getValue(group.get(i).jbmcVarname.substring(0, group.get(i).jbmcVarname.indexOf("[")));
                        group.get(i).guessedValue = o;
                        group.get(i).guess = group.get(i).guess.substring(0, group.get(i).guess.indexOf("["));
                    } else {
                        Object o = getValue(group.get(i).jbmcVarname);
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

    private String simplifyKetList(List<ket> ketListSameCoeff, int dim){
        String fin = "";
        StringBuilder res = new StringBuilder("");
        List<ket> helperList = new ArrayList<>(ketListSameCoeff);
        List<Integer> bitpositions = new ArrayList<>();

        for(int i = 0; i < ketListSameCoeff.size() - 1; i = i + 2){
            int checkInt = (ketListSameCoeff.get(i).bitIndex^ketListSameCoeff.get(i+1).bitIndex);
            if( checkInt != 0 && (checkInt & (checkInt-1))==0){
                helperList.remove(ketListSameCoeff.get(i));
                helperList.remove(ketListSameCoeff.get(i + 1));
                //exactly one bit is set => the numbers differ by only one bit
                int c;
                int bitposition = 0;
                while (checkInt != 0)
                {
                    c = checkInt & (0 - checkInt);
                    bitposition = Integer.numberOfTrailingZeros(c);
                    checkInt = checkInt ^ c;
                }
                bitpositions.add(bitposition);
                res = new StringBuilder("|" + String.format("%" + dim + "s", Integer.toBinaryString(ketListSameCoeff.get(i).bitIndex)).replace(' ', '0') + ">");
                res.setCharAt( res.length() - bitposition - 2, 'x');

            }else{
                //return unprocessed term
                for(int j = 0; j < helperList.size(); j++){
                    if (j == 0 && res.length() == 0) {
                        fin += "|" + String.format("%" + dim + "s", Integer.toBinaryString(helperList.get(j).bitIndex)).replace(' ', '0') + ">";
                        continue;
                    }
                    fin += " + " + "|" + String.format("%" + dim + "s", Integer.toBinaryString(helperList.get(j).bitIndex)).replace(' ', '0') + ">";

                }
                break;
            }

            if(fin == ""){
                fin += res.toString();
            }else{
                fin += " + ";
                fin += res.toString();
            }
        }


        if(bitpositions.size() == 2){
            if(bitpositions.get(0) == bitpositions.get(1)){
                res = new StringBuilder("|" + String.format("%" + dim + "s", Integer.toBinaryString(ketListSameCoeff.get(0).bitIndex)).replace(' ', '0') + ">");
                res.setCharAt( res.length() - bitpositions.get(0) - 2, 'x');
                res.setCharAt( res.length() - bitpositions.get(1) - 3, 'x');
            }
            fin = res.toString();
        }

        return fin;
    }

    private String simplifyQstate(List<ket> ketList, int dim){

        List<ket> ketListSameCoeff = new ArrayList<>();
        List<List<ket>> ketketList = new ArrayList<>();
        float currentCoeff = 0.0f;

        for(int i = 0; i < ketList.size(); i ++){
            currentCoeff = ketList.get(i).coeff;
            ketListSameCoeff.add(ketList.get(i));
            for(int j = i + 1; j < ketList.size(); j++){
                if(ketList.get(j).coeff == currentCoeff){
                    ketListSameCoeff.add(ketList.get(j));
                    ketList.remove(ketList.get(j));
                    j = j - 1;
                }
            }
            ketketList.add((List<ket>) ((ArrayList<ket>) ketListSameCoeff).clone());
            ketListSameCoeff.clear();
        }

        String valval = "";


        for(int i = 0; i < ketketList.size(); i++){
            if(ketketList.get(i).size() > 1){
                valval += Float.toString(ketketList.get(i).get(0).coeff) + " * (";
                valval += simplifyKetList(ketketList.get(i), dim);
                valval += ")";
            }else{
                for (int j = 0; j < ketketList.get(i).size(); j++) {
                    valval += Float.toString(ketketList.get(i).get(0).coeff) + " * ";
                    valval += "|" + String.format("%" + dim + "s", Integer.toBinaryString(ketketList.get(i).get(j).bitIndex)).replace(' ', '0') + ">";

                }
            }
        }


        valval += "----";



        for(int j = 0; j < ketketList.size(); j++) {

            String val = Float.toString(ketketList.get(j).get(0).coeff) + " * (";
            for (int i = 0; i < ketketList.get(j).size(); i++) {

                if (i == 0) {
                    val += "|" + String.format("%" + dim + "s", Integer.toBinaryString(ketketList.get(j).get(i).bitIndex)).replace(' ', '0') + ">";
                    continue;
                }
                val += " + " + "|" + String.format("%" + dim + "s", Integer.toBinaryString(ketketList.get(j).get(i).bitIndex)).replace(' ', '0') + ">";
            }

            val += ")";
            valval += val;
        }



        return valval;
    }

    private void createQuantumAss(Assignment qstate){
        List<Float> qvalues = new ArrayList<>();
        if(qstate.guessedValue == null) {
            return;
        } else {
            if(!(qstate.guessedValue instanceof ArrayList)) {
                return;
            }
            List<Object> values = (ArrayList<Object>)qstate.guessedValue;
            for(Object val : values) {
                if(val instanceof Float) {
                    qvalues.add((Float)val);
                } else if(val instanceof String) {
                    String sval = (String)val;
                    sval = sval.substring(sval.indexOf("/*") + 2, sval.indexOf("*/"));
                    sval = sval.trim();
                    qvalues.add(Float.parseFloat(sval));
                } else {
                    throw new RuntimeException("Error parsing qstate.");
                }
            }

        }
        int dim = qvalues.size();

        List<ket> ketList = new ArrayList<>();

        String val = "";
        for(int i = 0; i < qvalues.size(); i++){
            if(qvalues.get(i) > 0.0f || qvalues.get(i) < 0.0f){
                float coeff = qvalues.get(i);
                val += " + " + Float.toString(coeff) + " * " + "|" + String.format("%" + dim + "s", Integer.toBinaryString(i)).replace(' ', '0') + ">";

                ket k = new ket();
                k.coeff = coeff;
                k.bitIndex = i;
                ketList.add(k);
            }
        }
        ket k1 = new ket();
        k1.coeff = 0.3f;
        k1.bitIndex = 4;

        ket k2 = new ket();
        k2.coeff = 0.3f;
        k2.bitIndex = 1;
        //ketList.add(k1);
        //ketList.add(k2);

        String simplifiedVal = simplifyQstate(ketList, dim);
        val = val.substring(1);

        //Assignment ass = new Assignment(10, "", val, "q_state", "");
        qstate.guessedValue = val;
        qstate.guessedValue = simplifiedVal;
    }

    private List<Assignment> filterGroup(List<Assignment> group) {
        //group = group.stream().filter(a -> !a.value.contains("dynamic_object")).collect(Collectors.toList());
        LinkedHashMap<String, Assignment> groupMap = new LinkedHashMap<>();

        for (Assignment a : group) {
            groupMap.put(a.guess, a);
        }
        List<Assignment> filtered = new ArrayList<>(groupMap.values());

        for (Assignment a : filtered) {
            if(a.guess != null) {
                if (a.guess.startsWith("q_state_0")) {
                    createQuantumAss(a);
                }
            }
        }

        return filtered;
    }

    private Object findValue(String value, int maxIdx) {
        //all assignments in the same lane will be respected
        while(maxIdx < allAssignments.size() - 1 && allAssignments.get(maxIdx).lineNumber == allAssignments.get(maxIdx + 1).lineNumber) {
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
        if(value.startsWith("dynamic_object")) {
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
                    if(index >= valArray.size()) {
                        System.out.println("error updating array in trace.");
                    } else {
                        valArray.set(index, getValue(allAssignments.get(i).value));
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
                    //String guess = guessVariable(a.jbmcVarname);
                    String value = cleanValue(a.value);
                    //if (guess != null) {
                        //trackDynamicObject(guess, value);
                    //} else {
                        //trackDynamicObject(a.jbmcVarname, value);
                    //}
                    trackDynamicObject(a.jbmcVarname.substring(0, a.jbmcVarname.length() - 5), value);
                }
            }
        }
        for (int i = 0; i < lineAssignments.size(); ++i) {
            Assignment a = lineAssignments.get(i);
            if(a.jbmcVarname.startsWith("array_data_init")) {
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
        if(length <= 0) {
            return;
        }
        for(int i = idx; true; ++i) {
            Assignment a = lineAssignments.get(i);
            if(a.jbmcVarname.startsWith("new_array_item")) {
                a.jbmcVarname = arrayName + "[" + arrayIdx + "]";
            }
            if(a.jbmcVarname.startsWith("array_init_iter")) {
                int newIdx = -1;
                try {
                    newIdx = Integer.parseInt(a.value);
                } catch (Exception e) {
                    System.out.println("Error parsing trace.");
                }
                if(newIdx == length) {
                    break;
                } else {
                    arrayIdx = newIdx;
                }
            }
        }
    }

    private int findArrayLength(String arrayName, int startIdx, List<Assignment> assignments) {
        while(startIdx < assignments.size() - 1 && assignments.get(startIdx).lineNumber == assignments.get(startIdx + 1).lineNumber) {
            startIdx++;
        }
        while(arrayName.contains("array")) {
            arrayName = objectMap.get(arrayName);
            if(arrayName == null) {
                return -1;
            }
        }
        for(int i = startIdx; 0 <= i; --i) {
            if(assignments.get(i).jbmcVarname.equals(arrayName + ".length")) {
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
            if (object == null) {
                return lhs;
            }
            String res = lhs.replace(lhs.substring(0, lhs.indexOf(".")), object);
            if (res.endsWith(".data")) {
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
        if (object != null) {
            return applyObjectMap(object);
        }
        return lhs;
    }

    public String guessVariable(String lhs) {
        if (lhs == null) {
            return null;
        }
        //for (String s : TraceInformation.ignoredVars) {
         //   if (lhs.contains(s)) {
          //      return null;
           // }
        //}
        String res = applyObjectMap(lhs);
        String oldRes = null;
        while (!res.equals(oldRes)) {
            oldRes = res;
            res = applyObjectMap(res);
        }

        //for (String s : TraceInformation.ignoredVars) {
         //   if (res.contains(s)) {
          //      return null;
           // }
        //}
        //res = TraceInformation.applyExpressionMap(res);
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
                if (k.getValue().equals(object) && relevantVars.contains(k.getKey())) {
                    res += k.getKey() + " = ";
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

