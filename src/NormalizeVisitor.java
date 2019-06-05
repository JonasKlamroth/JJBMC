import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.UnaryTree;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;


import static org.jmlspecs.openjml.JmlTree.*;
import static com.sun.tools.javac.tree.JCTree.*;
/**
 * Created by jklamroth on 1/17/19.
 *
 * This Visitor will transform any supported JML-expression into negation normal form.
 */
public class NormalizeVisitor extends JmlTreeCopier {
    TranslationUtils transUtils = null;
    private boolean negated = false;
    private boolean selfNegated = false;

    public NormalizeVisitor(Context context, JmlTree.Maker maker) {
        super(context, maker);
        transUtils = new TranslationUtils(context, maker);
    }

    @Override
    public JCTree visitBinary(BinaryTree node, Void p) {
        JCBinary binary = (JCBinary)node;
        if(!negated) {
            boolean oldNeg = negated;
            boolean oldSelfNeg = selfNegated;
            JCExpression expr1 = super.copy((binary.getLeftOperand()));
            negated = oldNeg;
            selfNegated = oldSelfNeg;
            JCExpression expr2 = super.copy((binary.getRightOperand()));
            selfNegated = false;
            JCBinary b = M.Binary(((JCBinary) node).getTag(), expr1, expr2);
            b = (JCBinary)b.setType(binary.type);
            b.operator = binary.operator;
            return b;
        }
        if(binary.getTag() == Tag.AND) {
            negated = false;
            JCExpression expr1 = super.copy(negateExpression(binary.getLeftOperand()));
            negated = false;
            JCExpression expr2 = super.copy(negateExpression(binary.getRightOperand()));
            selfNegated = true;
            JCBinary b = M.Binary(Tag.OR, expr1, expr2); 
            b = (JCBinary)b.setType(binary.type);
            b.operator = binary.operator;
            return b;
        }
        if(binary.getTag() == Tag.OR) {
            negated = false;
            JCExpression expr1 = super.copy(negateExpression(binary.getLeftOperand()));
            negated = false;
            JCExpression expr2 = super.copy(negateExpression(binary.getRightOperand()));
            selfNegated = true;
            JCBinary b = M.Binary(Tag.AND, expr1, expr2); 
            b = (JCBinary)b.setType(binary.type);
            b.operator = binary.operator;
            return b;
        }
        return super.visitBinary(node, p);
    }

    @Override
    public JCTree visitJmlBinary(JmlBinary that, Void p) {
        JmlBinary binary = that;
        if(binary.getOp() == JmlTokenKind.IMPLIES) {
            if(negated) {
                negated = false;
                JCExpression expr1 = super.copy(binary.lhs);
                negated = false;
                JCExpression expr2 = super.copy(negateExpression(binary.rhs));
                selfNegated = true;
                JCBinary b = M.Binary(Tag.AND, expr1, expr2); 
                b = (JCBinary)b.setType(binary.type);
                return b;
            } else {
                negated = false;
                JCExpression expr1 = super.copy(negateExpression(binary.lhs));
                negated = false;
                JCExpression expr2 = super.copy(binary.rhs);
                selfNegated = true;
                JCBinary b = M.Binary(Tag.OR, expr1, expr2); 
                b = (JCBinary)b.setType(binary.type);
                return b;
            }
        }
        if(binary.getOp() == JmlTokenKind.REVERSE_IMPLIES) {
            if(!negated) {
                negated = false;
                JCExpression expr1 = super.copy(binary.lhs);
                negated = false;
                JCExpression expr2 = super.copy(negateExpression(binary.rhs));
                selfNegated = true;
                JCBinary b = M.Binary(Tag.OR, expr1, expr2); 
                b = (JCBinary)b.setType(binary.type);
                return b;
            } else {
                negated = false;
                JCExpression expr1 = super.copy(negateExpression(binary.lhs));
                negated = false;
                JCExpression expr2 = super.copy(binary.rhs);
                selfNegated = true;
                JCBinary b = M.Binary(Tag.AND, expr1, expr2); 
                b = (JCBinary)b.setType(binary.type);
                return b;
            }
        }
        if(binary.getOp() == JmlTokenKind.EQUIVALENCE) {
            negated = false;
            JCExpression expr1 = super.copy(binary.lhs);
            negated = false;
            JCExpression expr2 = super.copy(binary.rhs);
            selfNegated = true;
            if(negated) {
                JCBinary b = M.Binary(Tag.NE, expr1, expr2); 
                b = (JCBinary)b.setType(binary.type);
                return b;
            }
            JCBinary b = M.Binary(Tag.EQ, expr1, expr2); 
            b = (JCBinary)b.setType(binary.type);
            return b;
        }

        if(binary.getOp() == JmlTokenKind.INEQUIVALENCE) {
            negated = false;
            JCExpression expr1 = super.copy(binary.lhs);
            negated = false;
            JCExpression expr2 = super.copy(binary.rhs);
            selfNegated = true;
            if(negated) {
                JCBinary b = M.Binary(Tag.EQ, expr1, expr2); 
                b = (JCBinary)b.setType(binary.type);
                return b;
            }
            JCBinary b = M.Binary(Tag.NE, expr1, expr2); 
            b = (JCBinary)b.setType(binary.type);
            return b;
        }
        boolean oldNeg = negated;
        boolean oldSelfNeg = selfNegated;
        JCExpression expr1 = super.copy((JCExpression)binary.getLeftOperand());
        negated = oldNeg;
        selfNegated = oldSelfNeg;
        JCExpression expr2 = super.copy((JCExpression)binary.getRightOperand());
        selfNegated = false;
        JCBinary b = M.Binary(that.getTag(), expr1, expr2);
        b = (JCBinary)b.setType(binary.type);
        return b;
    }

    @Override
    public JCTree visitJmlQuantifiedExpr(JmlQuantifiedExpr that, Void p) {
        if(!negated) {
            return super.visitJmlQuantifiedExpr(that, p);
        }
        negated = false;
        JCExpression expr = super.copy(negateExpression(that.value));
        selfNegated = true;
        if(that.op == JmlTokenKind.BSEXISTS) {
            return M.JmlQuantifiedExpr(JmlTokenKind.BSFORALL, that.decls, that.range, expr);
        } else if(that.op == JmlTokenKind.BSFORALL) {
            return M.JmlQuantifiedExpr(JmlTokenKind.BSEXISTS, that.decls, that.range, expr);
        } else {
            throw new RuntimeException("Unknown quantifier type: " + that.op);
        }
    }

    @Override
    public JCTree visitUnary(UnaryTree node, Void p) {
        JCUnary unary = (JCUnary)node;
        if(unary.getTag() == Tag.NOT) {
            if(negated) {
                negated = false;
                return super.copy(unary.arg);
            } else {
                negated = true;
                JCExpression e = transUtils.unwrapExpression(unary.arg);
                JCExpression sub = super.copy(e);
                if(selfNegated) {
                    return sub;
                } else {
                    return negateExpression(sub);
                }
            }
        }
        return super.visitUnary(unary, p);
    }

    private JCUnary negateExpression(JCExpression expression) {
        JCUnary res = M.Unary(Tag.NOT, expression);
        res = (JCUnary)res.setType(expression.type);
        return res;
    }

    public static JCExpression normalize(JCExpression expression, Context context, Maker maker) {
        NormalizeVisitor normalizeVisitor = new NormalizeVisitor(context, maker);
        JCExpression ex = normalizeVisitor.copy(expression);
        return ex;
    }
}
