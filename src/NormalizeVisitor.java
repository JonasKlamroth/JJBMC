import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.UnaryTree;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Position;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeUtils;


import static org.jmlspecs.openjml.JmlTree.*;
import static com.sun.tools.javac.tree.JCTree.*;
/**
 * Created by jklamroth on 1/17/19.
 *
 * This Visitor will transform any supported JML-expression into negation normal form.
 */
public class NormalizeVisitor extends JmlTreeCopier {
    TranslationUtils transUtils = null;
    JmlTreeUtils treeutils = null;
    private boolean negated = false;
    private boolean selfNegated = false;

    public NormalizeVisitor(Context context, JmlTree.Maker maker) {
        super(context, maker);
        this.treeutils = JmlTreeUtils.instance(context);
    }

    @Override
    public JCTree visitBinary(BinaryTree node, Void p) {
        selfNegated = false;
        JCBinary binary = (JCBinary)node;
        if(binary.getTag() == Tag.EQ) {
            if(binary.rhs.type.getTag() == TypeTag.BOOLEAN) {
                boolean oldNegated = negated;
                JCExpression expr1 = super.copy(binary.getLeftOperand());
                negated = oldNegated;
                JCExpression expr2 = super.copy(binary.getRightOperand());
                JmlBinary b = treeutils.makeJmlBinary(Position.NOPOS, JmlTokenKind.EQUIVALENCE, expr1, expr2);
                negated = oldNegated;
                selfNegated = false;
                return super.copy(b);
            }
        }
        if(binary.getTag() == Tag.NE) {
            if(binary.rhs.type.getTag() == TypeTag.BOOLEAN) {
                boolean oldNegated = negated;
                JCExpression expr1 = super.copy(binary.getLeftOperand());
                negated = oldNegated;
                JCExpression expr2 = super.copy(binary.getRightOperand());
                JmlBinary b = treeutils.makeJmlBinary(Position.NOPOS, JmlTokenKind.INEQUIVALENCE, expr1, expr2);
                negated = oldNegated;
                selfNegated = false;
                return super.copy(b);
            }
        }
        if(!negated) {
            boolean oldNeg = negated;
            JCExpression expr1 = super.copy((binary.getLeftOperand()));
            negated = oldNeg;
            JCExpression expr2 = super.copy((binary.getRightOperand()));
            JCBinary b = M.Binary(((JCBinary) node).getTag(), expr1, expr2);
            b = (JCBinary)b.setType(binary.type);
            b.operator = binary.operator;
            negated = oldNeg;
            return b;
        }
        if(binary.getTag() == Tag.AND) {
            negated = false;
            JCExpression expr1 = super.copy(negateExpression(binary.getLeftOperand()));
            negated = false;
            JCExpression expr2 = super.copy(negateExpression(binary.getRightOperand()));
            JCBinary b = M.Binary(Tag.OR, expr1, expr2);
            b = (JCBinary)b.setType(binary.type);
            b.operator = binary.operator;
            selfNegated = true;
            return b;
        }
        if(binary.getTag() == Tag.OR) {
            JCExpression expr = negateExpression(binary.getLeftOperand());
            negated = false;
            JCExpression expr1 = super.copy(expr);
            negated = false;
            expr = negateExpression(binary.getRightOperand());
            JCExpression expr2 = super.copy(expr);
            JCBinary b = M.Binary(Tag.AND, expr1, expr2);
            b = (JCBinary)b.setType(binary.type);
            b.operator = binary.operator;
            selfNegated = true;
            return b;
        }

        return super.visitBinary(node, p);
    }

    @Override
    public JCTree visitJmlBinary(JmlBinary that, Void p) {
        selfNegated = false;
        JmlBinary binary = that;
        if(binary.getOp() == JmlTokenKind.IMPLIES) {
            if(negated) {
                negated = false;
                JCExpression expr1 = super.copy(binary.lhs);
                negated = false;
                JCExpression expr = negateExpression(binary.rhs);
                JCExpression expr2 = super.copy(expr);
                JCBinary b = M.Binary(Tag.AND, expr1, expr2);
                b = (JCBinary)b.setType(binary.type);
                selfNegated = true;
                return b;
            } else {
                JCExpression expr = negateExpression(binary.lhs);
                JCExpression expr1 = super.copy(expr);
                negated = false;
                JCExpression expr2 = super.copy(binary.rhs);
                JCBinary b = M.Binary(Tag.OR, expr1, expr2);
                b = (JCBinary)b.setType(binary.type);
                return b;
            }
        }
        if(binary.getOp() == JmlTokenKind.REVERSE_IMPLIES) {
            if(!negated) {
                JCExpression expr1 = super.copy(binary.lhs);
                negated = false;
                JCExpression expr = negateExpression(binary.rhs);
                JCExpression expr2 = super.copy(expr);
                JCBinary b = M.Binary(Tag.OR, expr1, expr2);
                b = (JCBinary)b.setType(binary.type);
                return b;
            } else {
                JCExpression expr = negateExpression(binary.lhs);
                JCExpression expr1 = super.copy(expr);
                negated = true;
                JCExpression expr2 = super.copy(binary.rhs);
                JCBinary b = M.Binary(Tag.AND, expr1, expr2);
                b = (JCBinary)b.setType(binary.type);
                return b;
            }
        }
        if(JmlTokenKind.EQUIVALENCE == binary.getOp()) {
            boolean oldNegated = negated;
            negated = false;
            JCExpression expr1 = super.copy(binary.lhs);
            negated = false;
            JCExpression expr2 = super.copy(binary.rhs);
            JmlBinary b = treeutils.makeJmlBinary(Position.NOPOS, JmlTokenKind.IMPLIES, expr1, expr2);
            JmlBinary b1 = treeutils.makeJmlBinary(Position.NOPOS, JmlTokenKind.IMPLIES, expr2, expr1);
            JCBinary b2 = M.Binary(Tag.AND, b, b1);
            b2.setType(binary.type);
            negated = oldNegated;
            JCExpression expr = super.copy(b2);
            selfNegated = true;
            return expr;
        }

        if(binary.getOp() == JmlTokenKind.INEQUIVALENCE) {
            JmlBinary bin = M.JmlBinary(JmlTokenKind.EQUIVALENCE, binary.lhs, binary.rhs);
            JCExpression expr = negateExpression(bin);
            return super.copy(expr);
        }
        boolean oldNeg = negated;
        JCExpression expr1 = super.copy((JCExpression)binary.getLeftOperand());
        negated = oldNeg;
        JCExpression expr2 = super.copy((JCExpression)binary.getRightOperand());
        JCBinary b = M.Binary(that.getTag(), expr1, expr2);
        b = (JCBinary)b.setType(binary.type);
        return b;
    }

    @Override
    public JCTree visitJmlQuantifiedExpr(JmlQuantifiedExpr that, Void p) {
        selfNegated =  false;
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
        selfNegated = false;
        JCUnary unary = (JCUnary)node;
        if(unary.getTag() == Tag.NOT) {
            if(negated) {
                JCExpression copy = super.copy(unary.arg);
                negated = false;
                if(selfNegated) {
                    selfNegated = false;
                    return unary;
                }
                selfNegated = true;
                return copy;
            } else {
                negated = true;
                JCExpression e = TranslationUtils.unwrapExpression(unary.arg);
                JCExpression sub = super.copy(e);
                if(selfNegated) {
                    selfNegated = false;
                    return sub;
                }
                return negateExpression(sub);
            }
        }
        return super.visitUnary(unary, p);
    }

    private JCExpression negateExpression(JCExpression expression) {
        if(expression instanceof JCUnary && expression.getTag() == Tag.NOT) {
            return ((JCUnary) expression).arg;
        }
        JCUnary res = M.Unary(Tag.NOT, expression);
        res = (JCUnary)res.setType(expression.type);
        return res;
    }

    public static JCExpression normalize(JCExpression expression, Context context, Maker maker) {
        NormalizeVisitor normalizeVisitor = new NormalizeVisitor(context, maker);
        return normalizeVisitor.copy(expression);
    }
}
