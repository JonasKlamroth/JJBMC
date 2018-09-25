import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;

public class DefaultReplaceVisitor extends JmlTreeCopier {

    public DefaultReplaceVisitor(Context context, JmlTree.Maker maker) {
        super(context, maker);
    }

    @Override
    public JCTree visitJmlMethodClauseExpr(JmlTree.JmlMethodClauseExpr that, Void p) {
        System.out.println("yeah");
        JCTree.JCExpression expression = that.expression;
        if(that.token == JmlTokenKind.ENSURES) {
            return this.M.JmlMethodClauseExpr(JmlTokenKind.REQUIRES, expression);
        } else {
            return this.M.JmlMethodClauseExpr(JmlTokenKind.ENSURES, expression);
        }
    }
}