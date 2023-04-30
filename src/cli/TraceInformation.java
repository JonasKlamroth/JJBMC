package cli;

import com.github.javaparser.utils.Pair;
import exceptions.TranslationException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

public class TraceInformation {
    public static final List<String> ignoredVars = new ArrayList<>(Arrays.asList("enableAssume",
        "enableNondet",
        "(void *)",
        "nondet_array_length",
        "array_data_init",
        "array_init_iter",
        "new_array_item",
        "malloc",
        "@class_identifier",
        "tmp",
        "assertionsDisabled"));
    private static final SortedMap<Integer, Integer> lineMap = new TreeMap<>();
    private static final SortedMap<Integer, String> methods = new TreeMap<>();
    private static final SortedMap<Integer, Set<String>> assertVars = new TreeMap<>();
    private static final SortedMap<Integer, String> asserts = new TreeMap<>();
    private static final Map<String, String> expressionMap = new HashMap<>();

    public static void reset() {
        lineMap.clear();
        methods.clear();
        asserts.clear();
        assertVars.clear();
        expressionMap.clear();
    }

    public static boolean isRelevantValue(String value) {
        if (value.contains("@class_identifier")) {
            return false;
        }
        return true;
        //return !value.contains("{");
        //if (value.contains("dynamic")) {
        //return false;
        //}
    }

    public static String getMethod(int lineNumber) {
        return methods.get(lineNumber);
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

    public static void addLineEquality(int printed, int orig) {
        lineMap.put(printed, orig);
    }

    public static void setExpressionMap(Map<String, String> expressionMap) {
        TraceInformation.expressionMap.clear();
        TraceInformation.expressionMap.putAll(expressionMap);
    }

    public static void addMethod(int line, String name) {
        methods.put(line, name);
    }

    public static void addAssert(int line, String ass) {
        asserts.put(line, ass);
    }

    public static void addAssertVars(int line, Set<String> vars) {
        assertVars.put(line, vars);
    }

    public static int getStartingLineForMethodAt(int line) {
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


    public static String getAssertForLine(int line) {
        if (!asserts.containsKey(line)) {
            throw new TranslationException("Tried to access assert for line " + line + " but found none.");
        }

        return asserts.get(line);
    }


    public static int getOriginalLine(int line) {
        if (!lineMap.containsKey(line)) {
            return -1;
        }
        return lineMap.get(line);
    }

    public static Set<String> getAssertVarsForLine(int line) {
        if (!assertVars.containsKey(line)) {
            throw new RuntimeException("No assert found in line: " + line + " but requested variables for it.");
        }
        return assertVars.get(line);
    }

    public static Pair<Integer, Integer> getRelevantRange(int lineIn) {
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

    public static boolean isActualNewLine(int oldLine, int newLine) {
        Pair<Integer, Integer> range = getRelevantRange(oldLine);
        return newLine != oldLine && newLine >= range.a && newLine < range.b;
    }


    private void addRelevantVar(String guess, int lineNumber) {
        Pair<Integer, Integer> range = getRelevantRange(lineNumber);
        for (int i = range.a; i <= range.b; ++i) {
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

    public static String cleanValue(String value) {
        value = value.trim();
        if (value.startsWith("(") && value.endsWith(")")) {
            value = value.substring(1, value.length() - 1);
        }
        if (value.startsWith("(void *)")) {
            value = value.substring(8);
        }
        if (value.startsWith("&")) {
            value = value.substring(1);
        }
        if (value.endsWith("[0L]")) {
            value = value.substring(0, value.length() - 4);
        }
        return value;
    }

    public static String cleanLHS(String lhs) {
        if (lhs.startsWith("(") && lhs.endsWith(")")) {
            lhs = lhs.substring(1, lhs.length() - 1);
        }
        if (lhs.startsWith("(void *)")) {
            lhs = lhs.substring(8);
        }
        if (lhs.startsWith("&")) {
            lhs = lhs.substring(1);
        }
        return lhs;
    }


    public static String applyExpressionMap(String lhs) {
        expressionMap.put("returnVar", "\\result");
        if (lhs == null) {
            return null;
        }
        String res = lhs;
        for (String s : expressionMap.keySet()) {
            res = res.replace(s, expressionMap.get(s));
        }
        return res;
    }

}
