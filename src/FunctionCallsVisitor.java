import com.sun.source.tree.MethodInvocationTree;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;

import java.util.HashSet;
import java.util.Set;

/**
 * Created by jklamroth on 12/17/18.
 */
public class FunctionCallsVisitor extends JmlTreeCopier {
    private Set<String> calledFunctions = new HashSet<>();
    private Set<String> specifiedFunctions = new HashSet<>();
    private List<JCTree.JCExpression> assignables = List.nil();
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
                foundNothing = true;
            } else {
                for(JCTree.JCExpression e : that.list) {
                    if (!assignables.contains(e)) {
                        assignables = assignables.append(e);
                    }
                }
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
        if(copy.specsDecl.cases != null) {
            specifiedFunctions.add(that.getName().toString());
        }
        //copy.cases = (JmlMethodSpecs)this.copy((JCTree)that.cases, (Object)p);
        copy.methodSpecsCombined = JmlSpecs.copy(that.methodSpecsCombined, p, this);
        copy.cases = (JmlTree.JmlMethodSpecs)copy.methodSpecsCombined.cases.clone();
        copy.type = that.type;


        if(TranslationUtils.isPure(currentMethod)) {
            foundNothing = true;
            specifiedFunctions.add(that.getName().toString());
        }

        if(assignables.size() == 0 && !foundNothing) {
            assignables = assignables.append(M.JmlStoreRefKeyword(JmlTokenKind.BSEVERYTHING));
        }
        return copy;
    }

    public Set<String> getCalledFunctions() {
        calledFunctions.retainAll(specifiedFunctions);
        return calledFunctions;
    }

    public List<JCTree.JCExpression> getAssignables() {
        return assignables;
    }

    public void resetAssignables() {
        assignables = List.nil();
    }
}
