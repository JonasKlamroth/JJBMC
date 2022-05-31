package utils;

import Exceptions.UnsupportedException;
import com.sun.source.tree.Tree;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;

public class RangeExtractor extends JmlTreeScanner {
    private final JmlTree.Maker maker;
    private JCTree.JCExpression minResult;
    private JCTree.JCExpression maxResult;
    private final Symbol ident;

    public RangeExtractor(JmlTree.Maker maker, Symbol ident) {
        this.ident = ident;
        this.maker = maker;
    }

    @Override
    public void visitBinary(JCTree.JCBinary tree) {
        if (tree.getKind() == Tree.Kind.GREATER_THAN) {
            if (tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent) tree.getLeftOperand()).name.equals(ident.name)) {
                if (minResult != null) {
                    throw new UnsupportedException("Ambiguous lower bound in range: ");
                }
                minResult = maker.Binary(JCTree.Tag.PLUS, tree.getRightOperand(), maker.Literal(1));
                return;
            }
            if (tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent) tree.getRightOperand()).name.equals(ident.name)) {
                if (maxResult != null) {
                    throw new UnsupportedException("Ambiguous upper bound in range: ");
                }
                maxResult = maker.Binary(JCTree.Tag.MINUS, tree.getLeftOperand(), maker.Literal(1));
                return;
            }
            throw new UnsupportedException("Error extracting range from quantifier: ");
        } else if (tree.getKind() == Tree.Kind.LESS_THAN) {
            if (tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent) tree.getLeftOperand()).name.equals(ident.name)) {
                if (maxResult != null) {
                    throw new UnsupportedException("Ambiguous upper bound in range: ");
                }
                maxResult = maker.Binary(JCTree.Tag.MINUS, tree.getRightOperand(), maker.Literal(1));
                return;
            }
            if (tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent) tree.getRightOperand()).name.equals(ident.name)) {
                if (minResult != null) {
                    throw new UnsupportedException("Ambiguous lower bound in range: ");
                }
                minResult = maker.Binary(JCTree.Tag.PLUS, tree.getLeftOperand(), maker.Literal(1));
                return;
            }
            throw new UnsupportedException("Error extracting range from quantifier: ");
        } else if (tree.getKind() == Tree.Kind.GREATER_THAN_EQUAL) {
            if (tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent) tree.getLeftOperand()).name.equals(ident.name)) {
                if (minResult != null) {
                    throw new UnsupportedException("Ambiguous lower bound in range: ");
                }
                minResult = tree.getRightOperand();
                return;
            }
            if (tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent) tree.getRightOperand()).name.equals(ident.name)) {
                if (maxResult != null) {
                    throw new UnsupportedException("Ambiguous upper bound in range: ");
                }
                maxResult = tree.getLeftOperand();
                return;
            }
            throw new UnsupportedException("Error extracting range from quantifier: ");
        } else if (tree.getKind() == Tree.Kind.LESS_THAN_EQUAL) {
            if (tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent) tree.getLeftOperand()).name.equals(ident.name)) {
                if (maxResult != null) {
                    throw new UnsupportedException("Ambiguous upper bound in range: ");
                }
                maxResult = tree.getRightOperand();
                return;
            }
            if (tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER && ((JCTree.JCIdent) tree.getRightOperand()).name.equals(ident.name)) {
                if (minResult != null) {
                    throw new UnsupportedException("Ambiguous lower bound in range: ");
                }
                minResult = tree.getLeftOperand();
                return;
            }
            throw new UnsupportedException("Error extracting range from quantifier: ");
        } else if (tree.getKind() == Tree.Kind.AND || tree.getKind() == Tree.Kind.CONDITIONAL_AND) {
            super.visitBinary(tree);
            return;
        }
        throw new UnsupportedException("Error extracting range from quantifier: " + tree);
    }


    public JCTree.JCExpression getMin() {
        if (minResult == null) {
            throw new UnsupportedException("No lower bound for quantified variable found.");
        }
        return minResult;
    }

    public JCTree.JCExpression getMax() {
        if (maxResult == null) {
            throw new UnsupportedException("No upper bound for quantified variable found.");
        }
        return maxResult;
    }

    public void extractRange(JCTree tree) {
        try {
            maxResult = null;
            minResult = null;
            super.scan(tree);
        } catch (UnsupportedException e) {
            throw new UnsupportedException(e.getInnerMessage() + tree);
        }
        if (maxResult == null || minResult == null) {
            throw new UnsupportedException("Could not extract bound from range for expr: " + tree.toString());
        }
    }
}

