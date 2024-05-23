package utils;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
import org.jmlspecs.openjml.JmlTreeScanner;

public class IdentVisitor extends JmlTreeScanner {
    private List<JCTree.JCIdent> idents = List.nil();
    private List<Symbol> syms = List.nil();

    public static List<JCTree.JCIdent> getIdents(JCTree.JCExpression expr) {
        IdentVisitor visitor = new IdentVisitor();
        visitor.scan(expr);
        return visitor.idents;
    }

    public static List<Symbol> getIdentSymbols(JCTree.JCExpression expr) {
        IdentVisitor visitor = new IdentVisitor();
        visitor.scan(expr);
        return visitor.syms;
    }

    @Override
    public void visitIdent(JCTree.JCIdent ident) {
        idents = idents.append(ident);
        syms = syms.append(ident.sym);
        super.visitIdent(ident);
    }
}
