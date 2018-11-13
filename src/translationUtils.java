import com.sun.tools.javac.tree.JCTree;
import org.jmlspecs.openjml.JmlTree;

/**
 * Created by jklamroth on 11/13/18.
 */
public class translationUtils {
    static JCTree.JCStatement makeAssumeStatement(JCTree.JCExpression expr, JmlTree.Maker M) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess assumeFunc = M.Select(classCProver, M.Name("assume"));
        JCTree.JCExpression args[] = new JCTree.JCExpression[]{expr};
        com.sun.tools.javac.util.List<JCTree.JCExpression> largs = com.sun.tools.javac.util.List.from(args);
        return M.Exec(
                M.Apply(com.sun.tools.javac.util.List.nil(), assumeFunc, largs));
    }
}
