package jjbmc.jml2java;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.EnclosedExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import jjbmc.UnsupportedException;
import org.jspecify.annotations.Nullable;

public class NormalizeBinaryExpressions extends ModifierVisitor<@Nullable Object> {

    private Expression swapOperator(BinaryExpr expr, BinaryExpr.Operator newOp) {
        Expression left = (Expression) expr.getLeft().accept(this, null);
        Expression right = (Expression) expr.getRight().accept(this, null);
        Expression newExpr = new BinaryExpr(left, right, newOp);
        newExpr.setParentNode(expr.getParentNode().get());
        left.setParentNode(newExpr);
        right.setParentNode(newExpr);
        return newExpr;
    }

    private Expression addNot(Expression expr) {
        Node oldParentNode = expr.getParentNode().get();
        Expression inner = (Expression) expr.accept(this, null);
        Expression newExpr = new UnaryExpr(new EnclosedExpr(inner), UnaryExpr.Operator.LOGICAL_COMPLEMENT);
        newExpr.setParentNode(oldParentNode);
        return newExpr;
    }

    private JmlQuantifiedExpr.JmlDefaultBinder getDualQuantifier(JmlQuantifiedExpr.JmlBinder quantifier) {
        if(quantifier.equals(JmlQuantifiedExpr.JmlDefaultBinder.FORALL)) {
            return JmlQuantifiedExpr.JmlDefaultBinder.EXISTS;
        }
        if(quantifier.equals(JmlQuantifiedExpr.JmlDefaultBinder.EXISTS)) {
            return JmlQuantifiedExpr.JmlDefaultBinder.FORALL;
        }
        throw new UnsupportedException("Quantifier " + quantifier + " not supported.");
    }

    @Override
    public Visitable visit(BinaryExpr n, Object arg) {
        if(n.getOperator().equals(BinaryExpr.Operator.ANTIVALENCE)) {
            return swapOperator(n, BinaryExpr.Operator.NOT_EQUALS);
        }
        return super.visit(n, arg);
    }

    @Override
    public Visitable visit(UnaryExpr n, Object arg) {
        if(n.getOperator().equals(UnaryExpr.Operator.LOGICAL_COMPLEMENT)) {
            if(n.getChildNodes().get(0) instanceof JmlQuantifiedExpr) {
                JmlQuantifiedExpr quantifiedExpression = (JmlQuantifiedExpr) n.getChildNodes().get(0);
                Expression inner = quantifiedExpression.getExpressions().getLast().get();
                inner = addNot(inner);
                NodeList<Expression> expressions = new NodeList<>();
                expressions.addAll(quantifiedExpression.getExpressions().subList(0, quantifiedExpression.getExpressions().size() - 1));
                expressions.add(inner);
                JmlQuantifiedExpr newQuantifiedExpr = new JmlQuantifiedExpr(quantifiedExpression.getTokenRange().get(),
                        getDualQuantifier(quantifiedExpression.getBinder()),
                        quantifiedExpression.getVariables(),
                        expressions);
                newQuantifiedExpr.setParentNode(n.getParentNode().get());
                return super.visit(newQuantifiedExpr, arg);
            }
        }
        return super.visit(n, arg);
    }
}
