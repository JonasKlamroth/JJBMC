package translation.jml2java;

import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.Statement;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NonNull;

import java.util.Stack;

/**
 * Transformation of JML expressions into equivalent Java code.
 *
 * @author Alexander Weigl
 * @version 1 (04.10.22)
 */
public class Jml2JavaFacade {
    @Data
    @AllArgsConstructor
    static class Result {
        @NonNull
        NodeList<Statement> statements = new NodeList<>();
        @NonNull
        Expression value;

        public Result(@NonNull Expression e) {
            this.value = e;
        }
    }
    public static Result translate(Expression expression, TranslationMode mode) {
        Jml2JavaExpressionTranslator j2jt = new Jml2JavaExpressionTranslator();
        return j2jt.accept(expression, mode);
    }

    public static BlockStmt embeddLoopInvariant(ForStmt stmt) {
        return null;
    }

    public static boolean containsJmlExpression(Expression expression) {
        Stack<Expression> search = new Stack<>();
        search.add(expression);

        while (!search.isEmpty()) {
            Expression e = search.pop();
            if (e instanceof Jmlish) {
                return true;
            }

            if (e instanceof BinaryExpr be) {
                if (be.getOperator() == BinaryExpr.Operator.IMPLICATION)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.RIMPLICATION)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.EQUIVALENCE)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.SUB_LOCK)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.SUB_LOCKE)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.SUBTYPE)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.RANGE)
                    return true;
            }

            for (Node childNode : e.getChildNodes()) {
                if (childNode instanceof Expression ex)
                    search.add(ex);
            }
        }
        return false;
    }
}
