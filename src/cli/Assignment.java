package cli;


public class Assignment {
    public String parameterName;
    public int lineNumber;
    public String value;
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
        return "in line " + lineNumber + ": " + TraceInformation.applyExpressionMap(this.guess) + " (" + jbmcVarname + ") = " + value;
    }

    public String getJbmcVarname() {
        return jbmcVarname;
    }

    public void setJbmcVarname(String jbmcVarname) {
        this.jbmcVarname = jbmcVarname;
    }
}
