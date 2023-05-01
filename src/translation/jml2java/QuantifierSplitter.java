package translation.jml2java;

import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr;

public class QuantifierSplitter {
    public Parameter getVariable(JmlQuantifiedExpr n) {
        if (n.getVariables().size() != 1) {
            throw new IllegalStateException("Unsupported number of variables.");
        }
        return n.getVariables().getFirst().get();
    }

    public Expression getLowerBound(JmlQuantifiedExpr n) {
        var expr = n.getExpressions().get(0);
        if (expr instanceof BinaryExpr be
                && be.getOperator() == BinaryExpr.Operator.AND) {
            var left = be.getLeft();
            if (left instanceof BinaryExpr le
                    && le.getOperator() == BinaryExpr.Operator.LESS_EQUALS) {
                return le.getLeft();
            }
        }
        throw new IllegalStateException("Mis-formed binder guard.");
    }

    public Expression getUpperBound(JmlQuantifiedExpr n) {
        var expr = n.getExpressions().get(0);
        if (expr instanceof BinaryExpr be
                && be.getOperator() == BinaryExpr.Operator.AND) {
            var right = be.getRight();
            if (right instanceof BinaryExpr re
                    && re.getOperator() == BinaryExpr.Operator.GREATER) {
                return re.getRight();
            }
        }
        throw new IllegalStateException("Mis-formed binder guard.");
    }
}
