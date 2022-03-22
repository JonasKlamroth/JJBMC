import com.sun.tools.javac.util.Pair;

import java.util.*;

public class TraceInformation {
    private static final List<String> ignoredVars = Arrays.asList("(void *)", "nondet_array_length", "array_data_init", "array_init_iter", "new_array_item", "malloc", "@class_identifier", "tmp", "assertionsDisabled");

    private final SortedMap<Integer, Integer> lineMap = new TreeMap<>();
    private final SortedMap<Integer, String> methods = new TreeMap<>();
    private final Map<String, List<String>> params = new HashMap<>();
    private final Map<String, List<String>> localVars = new HashMap<>();
    private final SortedMap<Integer, List<String>> assignments = new TreeMap<>();
    private final SortedMap<Integer, Set<String>> assertVars = new TreeMap<>();
    private final SortedMap<Integer, String> asserts = new TreeMap<>();
    private final Map<String, Boolean> isStaticMethod = new HashMap<>();
    private final Set<Integer> containsMethodCall = new HashSet<>();
    private final Map<String, String> objectMap = new HashMap<>();

    public void addLineEquality(int printed, int orig) {
        lineMap.put(printed, orig);
    }

    public void addMethod(int line, String name, boolean isStatic) {
        methods.put(line, name);
        params.put(name, new ArrayList<>());
        isStaticMethod.put(name, isStatic);
    }

    public void addMethodCall(int line) {
        containsMethodCall.add(line);
    }

    public void addAssert(int line, String ass) {
        asserts.put(line, ass);
    }

    public void addAssertVars(int line, Set<String> vars) {
        assertVars.put(line, vars);
    }


    public void addLocalVar(String var, String method) {
        if(!localVars.containsKey(method)) {
            localVars.put(method, new ArrayList<>());
        }
        localVars.get(method).add(var);
    }

    public void addParam(String param, String method) {
        params.get(method).add(param);
    }

    public void addAssignment(int line, String lhs) {
        if(assignments.containsKey(line)) {
            assignments.get(line).add(lhs);
        } else {
            assignments.put(line, new ArrayList<>());
            assignments.get(line).add(lhs);
        }
    }

    public int getStartingLineForMethodAt(int line) {
        int idx = methods.firstKey();
        for(int k : methods.keySet()) {
            if(line < k) {
                break;
            } else {
                idx = k;
            }
        }
        return idx;
    }

    public String getParamForLine(int line, int pos) {
        int methodLine = getStartingLineForMethodAt(line);
        String methodName = methods.get(methodLine);
        if(isStaticMethod.get(methodName)) {
            pos += 1;
        }
        if(!methods.containsKey(methodLine)) {
            throw new TranslationException("Searching parameter for function at line " + methodLine + " but no such function found.");
        }
        if(params.get(methods.get(methodLine)).size() <= pos) {
            throw new TranslationException("Tried to access " + pos + "th parameter of function " + methodLine + " but this function only has " + params.get(methods.get(methodLine)).size() + " parameter.");
        }
        if(params.get(methods.get(methodLine)).size() <= pos || pos < 0) {
            throw new TranslationException("Tried to get " + pos + "th parameter for function " + methods.get(methodLine) + " but has only " + params.get(methods.get(methodLine)).size());
        }
        return params.get(methods.get(methodLine)).get(pos);
    }


    public String getAssertForLine(int line) {
        if (!asserts.containsKey(line)) {
            throw new TranslationException("Tried to access assert for line " + line + " but found none.");
        }
        return asserts.get(line);
    }

    public List<String> getAssignmentForLine(int line) {
        if(!assignments.containsKey(line)) {
            throw new TranslationException("Tried to access assignments for line " + line + " but found none.");
        }
        return assignments.get(line);
    }

    public void trackDynamicObject(String name, String object) {
        if((!name.equals("this") || !objectMap.containsKey(object)) && !name.contains("new_tmp")) {
            objectMap.put(object, name);
        }
    }

    public int getOriginalLine(int line) {
        if(!lineMap.containsKey(line)) {
            return -1;
        }
        return lineMap.get(line);
    }

    public Set<String> getAssertVarsForLine(int line) {
        if(!assertVars.containsKey(line)) {
            throw new RuntimeException("No assert found in line: " + line + " but requested variables for it.");
        }
        return assertVars.get(line);
    }

    public Pair<Integer, Integer> getRelevantRange(int lineIn) {
        int begin = -1;
        for(int line : methods.keySet()) {
            if(line <= lineIn) {
                begin = line;
            } else {
                return new Pair<>(begin, line);
            }
        }
        return null;
    }

    public boolean containsMethodCall(int line) {
        return containsMethodCall.contains(line);
    }

    public void provideGuesses(List<JBMCOutput.Assignment> lineAssignments) {
        for(int i = lineAssignments.size() - 1; i >= 0; --i) {
            JBMCOutput.Assignment a = lineAssignments.get(i);
            if(isRelevantValue(a.value)) {
                if (a.value.startsWith("&dynamic_")) {
                    trackDynamicObject(a.jbmcVarname, a.value.substring(1));
                }
                if(a.jbmcVarname.endsWith("data") && a.value.startsWith("dynamic_") && a.value.endsWith("array")) {
                    String guess = guessVariable(a.jbmcVarname, a.lineNumber);
                    if(guess != null) {
                        trackDynamicObject(guess, a.value);
                    } else {
                        trackDynamicObject(a.jbmcVarname, a.value);
                    }
                }
            }
        }
        for(int i = lineAssignments.size() - 1; i >= 0; --i) {
            JBMCOutput.Assignment a = lineAssignments.get(i);
            if(isRelevantValue(a.value)) {
                a.guess = guessVariable(a.jbmcVarname, a.lineNumber);
            }
            a.lineNumber = this.getOriginalLine(a.lineNumber);
        }
        //}
    }


    private static boolean isRelevantValue(String value) {
        if(value.contains("@class_identifier")) {
            return false;
        }
        return !value.contains("{");
        //if(value.contains("dynamic")) {
            //return false;
        //}
    }

    private static boolean isRelevant(Set<String> relevantVars, String guess) {
        if(guess == null) {
            return false;
        }
        for(String s : relevantVars) {
            if(s.equals(guess)) {
                return true;
            }
            if(guess.contains("[") && guess.substring(0, guess.indexOf("[")).equals(s)) {
                return true;
            }
            if(guess.contains(".") && guess.substring(0, guess.indexOf(".")).equals(s)) {
                return true;
            }
        }
        return false;
    }

    public String guessVariable(String lhs, int line) {
        if(lhs == null) {
            return null;
        }
        for(String s : ignoredVars) {
            if(lhs.contains(s)) {
                return null;
            }
        }
        if(lhs.startsWith("arg")) {
            int pos = Integer.parseInt(lhs.substring(lhs.lastIndexOf("arg") + 3, lhs.length() - 1));
            if(containsMethodCall(line)) {
                return "param" + pos;
            }
        }
        String res = applyObjectMap(lhs);
        String oldRes = null;
        while (!res.equals(oldRes)) {
            oldRes = res;
            res = applyObjectMap(res);
        }

        for(String s : ignoredVars) {
            if(res.contains(s)) {
                return null;
            }
        }
        return res;
    }

    private String applyObjectMap(String lhs) {
        if(lhs.contains(".")) {
            String object = objectMap.get(lhs.substring(0, lhs.indexOf(".")));
            if(object == null) {
                return lhs;
            }
            return lhs.replace(lhs.substring(0, lhs.indexOf(".")), object);
        }
        if(lhs.contains("[")) {
            String object = objectMap.get(lhs.substring(0, lhs.indexOf("[")));
            if(object == null) {
                return lhs;
            }
            return lhs.replace(lhs.substring(0, lhs.indexOf("[")), object.substring(0, object.length()-5));
        }
        return lhs;
    }

}
