package jjbmc;


import jjbmc.trace.TraceInformation;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;
import org.jspecify.annotations.Nullable;

@Data
@AllArgsConstructor
@NoArgsConstructor
public class Assignment {
    private String parameterName;
    private int lineNumber;
    private String value;

    private @Nullable Object guessedValue;
    private @Nullable String guess;
    private String jbmcVarname;
    public Assignment(int line, String jbmcVarname, String value, String guess, String parameterName) {
        this(parameterName, line, value, null, guess, jbmcVarname);
    }
    @Override
    public String toString() {
        String val = guessedValue == null ? value : guessedValue.toString();
        String lhs = TraceInformation.applyExpressionMap(this.guess);
        return "in line " + lineNumber + ": " + lhs + " (" + jbmcVarname + ") = " + val;
    }
}
