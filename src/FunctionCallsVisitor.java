import com.sun.source.tree.MethodInvocationTree;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

/**
 * Created by jklamroth on 12/17/18.
 */
public class FunctionCallsVisitor extends JmlTreeCopier {
    public Set<String> calledFunctions = new HashSet<>();
    public List<JCTree.JCExpression> assignables = List.nil();
    private boolean foundNothing = false;
    JmlTree.JmlMethodDecl currentMethod = null;

    public FunctionCallsVisitor(Context context, JmlTree.Maker maker) {
        super(context, maker);
    }

    @Override
    public JCTree visitMethodInvocation(MethodInvocationTree that, Void p) {
        if(((JCTree.JCMethodInvocation)that).meth instanceof JCTree.JCIdent) {
            calledFunctions.add(((JCTree.JCIdent) ((JCTree.JCMethodInvocation)that).meth).getName().toString());
        } else if((((JCTree.JCMethodInvocation) that).meth instanceof JCTree.JCFieldAccess
                && ((JCTree.JCMethodInvocation) that).meth.type.getReturnType().equals(currentMethod.sym.owner.type))) {
            calledFunctions.add(((JCTree.JCFieldAccess) ((JCTree.JCMethodInvocation)that).meth).name.toString());
        }
        return super.visitMethodInvocation(that, p);
    }

    @Override
    public JCTree visitJmlMethodClauseStoreRef(JmlTree.JmlMethodClauseStoreRef that, Void p) {
        if(that.list != null) {
            if(that.list.stream().anyMatch(loc -> loc instanceof JmlTree.JmlStoreRefKeyword
                    && ((JmlTree.JmlStoreRefKeyword) loc).token.equals(JmlTokenKind.BSNOTHING))) {
                if(that.list.size() + assignables.size() > 1) {
                    throw new RuntimeException("Assignable containing \\nothing and something else is not valid.");
                }
                foundNothing = true;
            } else {
                assignables = assignables.appendList(that.list);
            }
        }
        return super.visitJmlMethodClauseStoreRef(that, p);
    }

    @Override
    public JCTree visitJmlMethodDecl(JmlTree.JmlMethodDecl that, Void p) {
        currentMethod = that;
        foundNothing = false;
        JmlTree.JmlMethodDecl copy = (JmlTree.JmlMethodDecl)super.visitJmlMethodDecl(that, p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl;
        //copy.cases = (JmlMethodSpecs)this.copy((JCTree)that.cases, (Object)p);
        copy.methodSpecsCombined = JmlSpecs.copy(that.methodSpecsCombined, p, this);
        copy.cases = (JmlTree.JmlMethodSpecs)copy.methodSpecsCombined.cases.clone();
        copy.type = that.type;
        if(assignables.size() == 0 && !foundNothing) {
            assignables = assignables.append(M.JmlStoreRefKeyword(JmlTokenKind.BSEVERYTHING));
        }
        return copy;
    }
}
