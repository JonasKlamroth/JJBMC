package utils;

import com.sun.source.tree.ArrayAccessTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;
import translation.BaseVisitor;

public class ReplaceVisitor extends JmlTreeCopier {
    static String oldName = null;
    static JCTree.JCExpression newExpression = null;

    public ReplaceVisitor(Context context, JmlTree.Maker maker) {
        super(context, maker);
    }

    public static JCTree.JCExpression replace(String oldName, JCTree.JCExpression newExpression, JCTree.JCExpression expr, JmlTree.Maker maker) {
        ReplaceVisitor.newExpression = newExpression;
        ReplaceVisitor.oldName = oldName;
        ReplaceVisitor rv = new ReplaceVisitor(BaseVisitor.context, BaseVisitor.M);
        return rv.copy(expr);
    }

    public static JCTree.JCStatement replace(String oldName, JCTree.JCExpression newExpression, JCTree.JCStatement expr, JmlTree.Maker maker) {
        ReplaceVisitor.newExpression = newExpression;
        ReplaceVisitor.oldName = oldName;
        ReplaceVisitor rv = new ReplaceVisitor(BaseVisitor.context, BaseVisitor.M);
        return rv.copy(expr);
    }

    public static JCTree.JCStatement replace(String oldName, String newName, JCTree.JCStatement expr, JmlTree.Maker maker) {
        ReplaceVisitor.newExpression = maker.Ident(newName);
        ReplaceVisitor.oldName = oldName;
        ReplaceVisitor rv = new ReplaceVisitor(BaseVisitor.context, BaseVisitor.M);
        JCTree.JCStatement st = rv.copy(expr);
        return st;
    }

    public static JCTree.JCExpression replace(String oldName, String newName, JCTree.JCExpression expr, JmlTree.Maker maker) {
        ReplaceVisitor.newExpression = maker.Ident(newName);
        ReplaceVisitor.oldName = oldName;
        ReplaceVisitor rv = new ReplaceVisitor(BaseVisitor.context, BaseVisitor.M);
        JCTree.JCExpression cpy = rv.copy(expr);
        return cpy;
    }

    @Override
    public JCTree visitIdentifier(IdentifierTree node, Void p) {
        JCTree.JCIdent t = (JCTree.JCIdent) super.visitIdentifier(node, p);
        if (t.getName().toString().equals(oldName)) {
            return newExpression;
        }
        return t;
    }

    @Override
    public JCTree visitArrayAccess(ArrayAccessTree node, Void p) {
        JCTree.JCArrayAccess a = (JCTree.JCArrayAccess) super.visitArrayAccess(node, p);
        if (a.indexed.toString().equals(oldName)) {
            a.indexed = newExpression;
        }
        return a;
    }

    @Override
    public JCTree visitJmlVariableDecl(JmlTree.JmlVariableDecl that, Void p) {
        JCTree.JCVariableDecl vd = (JCTree.JCVariableDecl) super.visitJmlVariableDecl(that, p);
        if (vd.name.toString().equals(oldName)) {
            return newExpression;
        }
        return vd;
    }
}

