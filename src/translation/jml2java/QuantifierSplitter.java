package translation.jml2java;

import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.jml.expr.JmlMultiCompareExpr;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr;

/**
 * Supports two formats:
 *
 * <ul>
 * <li>Bounded quantifier with three expressions:
 * {@code (\forall int i; lower; upper; val)}*
 * </li>
 * <li>Or range format with two expressions:
 * {@code (\forall int i; lower <= i && i < upper; val)}*
 * </li>
 * <li>Or range format with two expressions:
 * {@code (\forall int i; lower <= i < upper; val)}*
 * </li>
 * </ul>
 */
public class QuantifierSplitter {
    public Parameter getVariable(JmlQuantifiedExpr n) {
        if (n.getVariables().size() != 1) {
            throw new IllegalStateException("Unsupported number of variables.");
        }
        return n.getVariables().getFirst().get();
    }

    public Expression getLowerBound(JmlQuantifiedExpr n) {
        if (n.getExpressions().size() == 3) { // bounded format
            return n.getExpressions().get(0);
        }

        var expr = n.getExpressions().get(0);
        if (expr instanceof BinaryExpr be
                && be.getOperator() == BinaryExpr.Operator.AND) {
            var left = be.getLeft();
            if (left instanceof BinaryExpr le
                    && le.getOperator() == BinaryExpr.Operator.LESS_EQUALS) {
                return le.getLeft();
            }
        }
        if (expr instanceof JmlMultiCompareExpr me) {
            if (me.getOperators().get(0).equals(BinaryExpr.Operator.LESS_EQUALS)
                    && me.getOperators().get(0).equals(BinaryExpr.Operator.LESS)) {
                return me.getExpressions().getFirst().get();
            }
        }
        throw new IllegalStateException("Mis-formed binder guard.");
    }

    public Expression getUpperBound(JmlQuantifiedExpr n) {
        if (n.getExpressions().size() == 3) { // bounded format
            return n.getExpressions().get(1);
        }

        var expr = n.getExpressions().get(0);
        if (expr instanceof BinaryExpr be
                && be.getOperator() == BinaryExpr.Operator.AND) {
            var right = be.getRight();
            if (right instanceof BinaryExpr re
                    && re.getOperator() == BinaryExpr.Operator.LESS) {
                return re.getRight();
            }
        }

        if (expr instanceof JmlMultiCompareExpr me) {
            if (me.getOperators().get(0).equals(BinaryExpr.Operator.LESS_EQUALS)
                    && me.getOperators().get(0).equals(BinaryExpr.Operator.LESS)) {
                return me.getExpressions().getLast().get();
            }
        }
        throw new IllegalStateException("Mis-formed binder guard.");
    }
}
