import com.sun.source.tree.MethodInvocationTree;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

/**
 * Created by jklamroth on 12/17/18.
 */
public class FunctionCallsVisitor extends JmlTreeCopier {
    Set<String> calledFunctions = new HashSet<>();

    public FunctionCallsVisitor(Context context, JmlTree.Maker maker) {
        super(context, maker);
    }

    @Override
    public JCTree visitMethodInvocation(MethodInvocationTree that, Void p) {
        if(((JCTree.JCMethodInvocation)that).meth instanceof JCTree.JCIdent) {
            calledFunctions.add(((JCTree.JCIdent) ((JCTree.JCMethodInvocation)that).meth).getName().toString());
        }
        return super.visitMethodInvocation(that, p);
    }
}
