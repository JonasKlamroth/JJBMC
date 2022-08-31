package cli;


public class Assignment {
    public String parameterName;
    public int lineNumber;
    public String value;

    public Object guessedValue;
    public String guess;
    protected String jbmcVarname;

    public Assignment(int line, String jbmcVarname, String value, String guess, String parameterName) {
        this.parameterName = parameterName;
        this.lineNumber = line;
        this.setJbmcVarname(jbmcVarname);
        this.value = value;
        this.guess = guess;
    }

    @Override
    public String toString() {
        String val = guessedValue == null ? value : guessedValue.toString();
        String lhs = TraceInformation.applyExpressionMap(this.guess);
        return "in line " + lineNumber + ": " + lhs + " (" + jbmcVarname + ") = " + val;
    }

    public String getJbmcVarname() {
        return jbmcVarname;
    }

    public void setJbmcVarname(String jbmcVarname) {
        this.jbmcVarname = jbmcVarname;
    }
}
