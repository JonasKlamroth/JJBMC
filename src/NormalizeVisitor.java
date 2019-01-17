import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.UnaryTree;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;


import static org.jmlspecs.openjml.JmlTree.*;
import static com.sun.tools.javac.tree.JCTree.*;
/**
 * Created by jklamroth on 1/17/19.
 */
public class NormalizeVisitor extends JmlTreeCopier {
    TranslationUtils transUtils = null;
    private boolean negated = false;

    public NormalizeVisitor(Context context, JmlTree.Maker maker) {
        super(context, maker);
        transUtils = new TranslationUtils(context, maker);
    }

    @Override
    public JCTree visitBinary(BinaryTree node, Void p) {
        JCBinary binary = (JCBinary)node;
        if(!negated) {
            return super.visitBinary(binary, p);
        }
        if(binary.getTag() == Tag.AND) {
            negated = false;
            JCExpression expr1 = super.copy(M.Unary(Tag.NOT, binary.getLeftOperand()));
            negated = false;
            JCExpression expr2 = super.copy(M.Unary(Tag.NOT, binary.getRightOperand()));
            return M.Binary(Tag.OR, expr1, expr2);
        }
        if(binary.getTag() == Tag.OR) {
            negated = false;
            JCExpression expr1 = super.copy(M.Unary(Tag.NOT, binary.getLeftOperand()));
            negated = false;
            JCExpression expr2 = super.copy(M.Unary(Tag.NOT, binary.getRightOperand()));
            return M.Binary(Tag.AND, expr1, expr2);
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
                JCExpression expr2 = super.copy(M.Unary(Tag.NOT, binary.rhs));
                return M.Binary(Tag.AND, expr1, expr2);
            } else {
                negated = false;
                JCExpression expr1 = super.copy(M.Unary(Tag.NOT, binary.lhs));
                negated = false;
                JCExpression expr2 = super.copy(binary.rhs);
                return M.Binary(Tag.OR, expr1, expr2);
            }
        }
        if(binary.getOp() == JmlTokenKind.REVERSE_IMPLIES) {
            if(!negated) {
                negated = false;
                JCExpression expr1 = super.copy(binary.lhs);
                negated = false;
                JCExpression expr2 = super.copy(M.Unary(Tag.NOT, binary.rhs));
                return M.Binary(Tag.OR, expr1, expr2);
            } else {
                negated = false;
                JCExpression expr1 = super.copy(M.Unary(Tag.NOT, binary.lhs));
                negated = false;
                JCExpression expr2 = super.copy(binary.rhs);
                return M.Binary(Tag.AND, expr1, expr2);
            }
        }
        if(binary.getOp() == JmlTokenKind.EQUIVALENCE) {
            negated = false;
            JCExpression expr1 = super.copy(binary.lhs);
            negated = false;
            JCExpression expr2 = super.copy(binary.rhs);
            if(negated) {
                return M.Binary(Tag.NE, expr1, expr2);
            }
            return M.Binary(Tag.EQ, expr1, expr2);
        }

        if(binary.getOp() == JmlTokenKind.INEQUIVALENCE) {
            negated = false;
            JCExpression expr1 = super.copy(binary.lhs);
            negated = false;
            JCExpression expr2 = super.copy(binary.rhs);
            if(negated) {
                return M.Binary(Tag.EQ, expr1, expr2);
            }
            return M.Binary(Tag.NE, expr1, expr2);
        }
        return super.visitBinary(that, p);
    }

    @Override
    public JCTree visitJmlQuantifiedExpr(JmlQuantifiedExpr that, Void p) {
        if(!negated) {
            return super.visitJmlQuantifiedExpr(that, p);
        }
        negated = false;
        JCExpression expr = super.copy(M.Unary(Tag.NOT, that.value));
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
                if(e instanceof JmlQuantifiedExpr) {
                    return super.copy(unary.arg);
                }
            }
        }
        return super.visitUnary(unary, p);
    }

    public static JCExpression normalize(JCExpression expression, Context context, Maker maker) {
        NormalizeVisitor normalizeVisitor = new NormalizeVisitor(context, maker);
        return normalizeVisitor.copy(expression);
    }
}
