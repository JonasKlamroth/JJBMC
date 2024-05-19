package translation.jml2java;

import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.NameExpr;
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
    public static Parameter getVariable(JmlQuantifiedExpr n) {
        if (n.getVariables().size() != 1) {
            throw new IllegalStateException("Unsupported number of variables.");
        }
        return n.getVariables().getFirst().get();
    }

    private static Expression getUpperBound(BinaryExpr e, NameExpr variable) {
        if(e.getOperator().equals(BinaryExpr.Operator.AND)) {
            Expression leftCandidate = null;
            if(e.getLeft() instanceof BinaryExpr be) {
                leftCandidate = getUpperBound(be, variable);
            }
            Expression rightCandidate = null;
            if(e.getRight() instanceof BinaryExpr be) {
                rightCandidate = getUpperBound(be, variable);
            }
            if(rightCandidate == null && leftCandidate == null) {
                return null;
            }
            if(rightCandidate != null && leftCandidate != null) {
                throw new IllegalStateException("Ubiquitous lower bound found in: " + e);
            }
            if(rightCandidate != null) {
                return rightCandidate;
            }
            return leftCandidate;
        }

        if(e.getOperator().equals(BinaryExpr.Operator.LESS) && e.getLeft().equals(variable)) {
            return new BinaryExpr(e.getRight(), new IntegerLiteralExpr("1"), BinaryExpr.Operator.PLUS);
        }
        if(e.getOperator().equals(BinaryExpr.Operator.LESS_EQUALS) && e.getLeft().equals(variable)) {
            return e.getRight();
        }
        if(e.getOperator().equals(BinaryExpr.Operator.GREATER) && e.getRight().equals(variable)) {
            return new BinaryExpr(e.getLeft(), new IntegerLiteralExpr("1"), BinaryExpr.Operator.PLUS);
        }
        if(e.getOperator().equals(BinaryExpr.Operator.GREATER_EQUALS) && e.getRight().equals(variable)) {
            return e.getLeft();
        }
        return null;
    }

    private static Expression getUpperBound(JmlMultiCompareExpr expr, NameExpr variable) {
        if(expr.getExpressions().size() != 3 || expr.getOperators().size() != 2) {
            throw new IllegalStateException("Unable to find lower bound in: " + expr);
        }
        Expression firstCandidate = getUpperBound(new BinaryExpr(expr.getExpressions().get(0), expr.getExpressions().get(1), expr.getOperators().get(0)), variable);
        Expression secondCandidate = getUpperBound(new BinaryExpr(expr.getExpressions().get(1), expr.getExpressions().get(2), expr.getOperators().get(1)), variable);
        if(firstCandidate == null && secondCandidate == null) {
            return null;
        }
        if(firstCandidate != null && secondCandidate != null) {
            throw new IllegalStateException("Ubiquitous lower bound found in: " + expr);
        }
        if(firstCandidate != null) {
            return firstCandidate;
        }
        return secondCandidate;
    }

    private static Expression getLowerBound(BinaryExpr e, NameExpr variable) {
        if(e.getOperator().equals(BinaryExpr.Operator.AND)) {
            Expression leftCandidate = null;
            if(e.getLeft() instanceof BinaryExpr be) {
                leftCandidate = getLowerBound(be, variable);
            }
            Expression rightCandidate = null;
            if(e.getRight() instanceof BinaryExpr be) {
                rightCandidate = getLowerBound(be, variable);
            }
            if(rightCandidate == null && leftCandidate == null) {
                return null;
            }
            if(rightCandidate != null && leftCandidate != null) {
                throw new IllegalStateException("Ubiquitous lower bound found in: " + e);
            }
            if(rightCandidate != null) {
                return rightCandidate;
            }
            return leftCandidate;
        }

        if(e.getOperator().equals(BinaryExpr.Operator.LESS) && e.getRight().equals(variable)) {
            return new BinaryExpr(e.getLeft(), new IntegerLiteralExpr("1"), BinaryExpr.Operator.PLUS);
        }
        if(e.getOperator().equals(BinaryExpr.Operator.LESS_EQUALS) && e.getRight().equals(variable)) {
            return e.getLeft();
        }
        if(e.getOperator().equals(BinaryExpr.Operator.GREATER) && e.getLeft().equals(variable)) {
            return new BinaryExpr(e.getRight(), new IntegerLiteralExpr("1"), BinaryExpr.Operator.PLUS);
        }
        if(e.getOperator().equals(BinaryExpr.Operator.GREATER_EQUALS) && e.getLeft().equals(variable)) {
            return e.getRight();
        }
        return null;
    }

    private static Expression getLowerBound(JmlMultiCompareExpr expr, NameExpr variable) {
        if(expr.getExpressions().size() != 3 || expr.getOperators().size() != 2) {
            throw new IllegalStateException("Unable to find lower bound in: " + expr);
        }
        Expression firstCandidate = getLowerBound(new BinaryExpr(expr.getExpressions().get(0), expr.getExpressions().get(1), expr.getOperators().get(0)), variable);
        Expression secondCandidate = getLowerBound(new BinaryExpr(expr.getExpressions().get(1), expr.getExpressions().get(2), expr.getOperators().get(1)), variable);
        if(firstCandidate == null && secondCandidate == null) {
            return null;
        }
        if(firstCandidate != null && secondCandidate != null) {
            throw new IllegalStateException("Ubiquitous lower bound found in: " + expr);
        }
        if(firstCandidate != null) {
            return firstCandidate;
        }
        return secondCandidate;
    }

    public static Expression getLowerBound(JmlQuantifiedExpr n) {
        if (n.getExpressions().size() == 3) { // bounded format
            return n.getExpressions().get(0);
        }
        NameExpr variable = getVariable(n).getNameAsExpression();

        if(n.getExpressions().get(0) instanceof BinaryExpr be) {
            var res = getLowerBound(be, variable);
            if(res != null) {
                return res;
            }
        }
        if(n.getExpressions().get(0) instanceof JmlMultiCompareExpr be) {
            var res = getLowerBound(be, variable);
            if(res != null) {
                return res;
            }
        }
        throw new IllegalStateException("Mis-formed binder guard in: " + n);
    }

    public static Expression getUpperBound(JmlQuantifiedExpr n) {
        if (n.getExpressions().size() == 3) { // bounded format
            return n.getExpressions().get(0);
        }
        NameExpr variable = getVariable(n).getNameAsExpression();

        if (n.getExpressions().get(0) instanceof BinaryExpr be) {
            var res = getUpperBound(be, variable);
            if(res != null) {
                return res;
            }
        }
        if (n.getExpressions().get(0) instanceof JmlMultiCompareExpr be) {
            var res = getUpperBound(be, variable);
            if(res != null) {
                return res;
            }
        }
        throw new IllegalStateException("Mis-formed binder guard in: " + n);
    }
}
