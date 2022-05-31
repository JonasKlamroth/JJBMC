package cli;

import Exceptions.TranslationException;
import com.sun.tools.javac.util.Pair;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

public class TraceInformation {
    private static final List<String> ignoredVars = Arrays.asList("enableAssume",
            "enableNondet",
            "(void *)",
            "nondet_array_length",
            "array_data_init",
            "array_init_iter",
            "new_array_item",
            "malloc",
            "@class_identifier",
            "tmp",
            "assertionsDisabled");

    private Map<String, String> expressionMap = new HashMap<>();
    private final SortedMap<Integer, Integer> lineMap = new TreeMap<>();
    private final SortedMap<Integer, String> methods = new TreeMap<>();
    private final SortedMap<Integer, Set<String>> assertVars = new TreeMap<>();
    private final SortedMap<Integer, String> asserts = new TreeMap<>();
    private final Map<String, String> objectMap = new HashMap<>();

    public void addLineEquality(int printed, int orig) {
        lineMap.put(printed, orig);
    }

    public void setExpressionMap(Map<String, String> expressionMap) {
        this.expressionMap = expressionMap;
    }

    public void addMethod(int line, String name) {
        methods.put(line, name);
    }

    public void addAssert(int line, String ass) {
        asserts.put(line, ass);
    }

    public void addAssertVars(int line, Set<String> vars) {
        assertVars.put(line, vars);
    }

    public int getStartingLineForMethodAt(int line) {
        int idx = methods.firstKey();
        for (int k : methods.keySet()) {
            if (line < k) {
                break;
            } else {
                idx = k;
            }
        }
        return idx;
    }

    public String getAssertForLine(int line) {
        if (!asserts.containsKey(line)) {
            throw new TranslationException("Tried to access assert for line " + line + " but found none.");
        }
        return asserts.get(line);
    }

    public void trackDynamicObject(String name, String object) {
        if ((!name.equals("this") || !objectMap.containsKey(object)) && !name.contains("new_tmp")) {
            objectMap.put(object, name);
        }
    }

    public int getOriginalLine(int line) {
        if (!lineMap.containsKey(line)) {
            return -1;
        }
        return lineMap.get(line);
    }

    public Set<String> getAssertVarsForLine(int line) {
        if (!assertVars.containsKey(line)) {
            throw new RuntimeException("No assert found in line: " + line + " but requested variables for it.");
        }
        return assertVars.get(line);
    }

    public Pair<Integer, Integer> getRelevantRange(int lineIn) {
        int begin = -1;
        for (int line : methods.keySet()) {
            if (line <= lineIn) {
                begin = line;
            } else {
                return new Pair<>(begin, line);
            }
        }
        return null;
    }

    public void provideGuesses(List<JBMCOutput.Assignment> lineAssignments) {
        String t = null;
        for (int i = lineAssignments.size() - 1; i >= 0; --i) {
            JBMCOutput.Assignment a = lineAssignments.get(i);
            if (isRelevantValue(a.value)) {
                if (a.value.startsWith("&dynamic_")) {
                    String value = cleanValue(a.value);
                    trackDynamicObject(a.jbmcVarname, value);
                }
                if (a.jbmcVarname.endsWith("data") && a.value.contains("dynamic_") && a.value.contains("_array")) {
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
            JBMCOutput.Assignment a = lineAssignments.get(i);
            if (isRelevantValue(a.value)) {
                a.guess = guessVariable(a.jbmcVarname);
                if (a.guess != null && a.parameterName != null) {
                    String method = methods.get(getStartingLineForMethodAt(a.lineNumber));
                    if (a.parameterName.contains(method)) {
                        addRelevantVar(a.guess, a.lineNumber);
                    }
                }
            }
            a.lineNumber = this.getOriginalLine(a.lineNumber);
        }
        //}
    }

    private void addRelevantVar(String guess, int lineNumber) {
        Pair<Integer, Integer> range = getRelevantRange(lineNumber);
        for (int i = range.fst; i <= range.snd; ++i) {
            try {
                Set<String> assertVarsForLine = getAssertVarsForLine(i);
                if (assertVarsForLine != null) {
                    assertVarsForLine.add(guess);
                }
            } catch (RuntimeException e) {
                //thats ok in this case
            }
        }
    }

    private String cleanValue(String value) {
        if (value.startsWith("&")) {
            value = value.substring(1);
        }
        if (value.startsWith("(") && value.endsWith(")")) {
            value = value.substring(1, value.length() - 1);
        }
        if (value.startsWith("(void *)")) {
            value = value.substring(8);
        }
        if (value.endsWith("[0L]")) {
            value = value.substring(0, value.length() - 4);
        }
        return value;
    }


    private static boolean isRelevantValue(String value) {
        if (value.contains("@class_identifier")) {
            return false;
        }
        return !value.contains("{");
        //if (value.contains("dynamic")) {
        //return false;
        //}
    }

    private static boolean isRelevant(Set<String> relevantVars, String guess) {
        if (guess == null) {
            return false;
        }
        for (String s : relevantVars) {
            if (s.equals(guess)) {
                return true;
            }
            if (guess.contains("[") && guess.substring(0, guess.indexOf("[")).equals(s)) {
                return true;
            }
            if (guess.contains(".") && guess.substring(0, guess.indexOf(".")).equals(s)) {
                return true;
            }
        }
        return false;
    }

    public String guessVariable(String lhs) {
        if (lhs == null) {
            return null;
        }
        for (String s : ignoredVars) {
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

        for (String s : ignoredVars) {
            if (res.contains(s)) {
                return null;
            }
        }
        res = applyExpressionMap(res);
        return res;
    }

    private String applyExpressionMap(String lhs) {
        String res = lhs;
        for (String s : expressionMap.keySet()) {
            res = res.replace(s, expressionMap.get(s));
        }
        return res;
    }

    private String applyObjectMap(String lhs) {
        if (lhs.contains(".")) {
            String object = objectMap.get(lhs.substring(0, lhs.indexOf(".")));
            if (object == null) {
                return lhs;
            }
            return lhs.replace(lhs.substring(0, lhs.indexOf(".")), object);
        }
        if (lhs.contains("[")) {
            String object = objectMap.get(lhs.substring(0, lhs.indexOf("[")));
            if (object == null) {
                return lhs;
            }
            if (object.endsWith(".data")) {
                return lhs.replace(lhs.substring(0, lhs.indexOf("[")), object.substring(0, object.length() - 5));
            }
            return lhs.replace(lhs.substring(0, lhs.indexOf("[")), object);

        }
        return lhs;
    }

}
