package translation;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.jml.clauses.JmlAccessibleClause;
import com.github.javaparser.ast.jml.clauses.JmlMultiExprClause;
import com.github.javaparser.ast.jml.clauses.JmlSimpleExprClause;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.sun.source.tree.MethodInvocationTree;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;


/**
 * Created by jklamroth on 12/17/18.
 */
public class FunctionCallsVisitor extends VoidVisitorAdapter<Object> {
    private MethodDeclaration currentMethod = null;
    private final Set<String> calledFunctions = new HashSet<>();
    private final Set<String> specifiedFunctions = new HashSet<>();
    private List<Expression> assignables = new LinkedList<>();
    private boolean foundNothing = false;

    @Override
    public void visit(MethodCallExpr that, Object arg) {
        calledFunctions.add(that.getNameAsString());
        /*
        if (that.getName() instanceof JCTree.JCIdent) {
        } else if ((((JCTree.JCMethodInvocation) that).meth instanceof JCTree.JCFieldAccess
                && ((JCTree.JCMethodInvocation) that).meth.type.getReturnType().equals(currentMethod.sym.owner.type))) {
            calledFunctions.add(((JCTree.JCFieldAccess) ((JCTree.JCMethodInvocation) that).meth).name.toString());
        }
        return super.visitMethodInvocation(that, p);*/
    }


    @Override
    public void visit(JmlMultiExprClause that, Object arg) {
        if (that.getExpressions() != null) {
            if (that.getExpressions().stream()
                    .anyMatch(loc -> loc.isNameExpr() && loc.asNameExpr().getNameAsString().endsWith("\\nothing"))) {
                foundNothing = true;
            } else {
                for (Expression e : that.getExpressions()) {
                    if (!assignables.contains(e)) {
                        assignables.add(e);
                    }
                }
            }
        }
    }

    @Override
    public JCTree visitJmlMethodDecl(JmlTree.JmlMethodDecl that, Void p) {
        currentMethod = that;
        foundNothing = false;

        JmlTree.JmlMethodDecl copy = (JmlTree.JmlMethodDecl) super.visitJmlMethodDecl(that, p);

        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl;
        if (copy.specsDecl.cases != null) {
            specifiedFunctions.add(that.getName().toString());
        }
        //copy.cases = (JmlMethodSpecs)this.copy((JCTree)that.cases, (Object)p);
        copy.methodSpecsCombined = JmlSpecs.copy(that.methodSpecsCombined, p, this);
        copy.cases = (JmlTree.JmlMethodSpecs) copy.methodSpecsCombined.cases.clone();
        copy.type = that.type;


        if (TranslationUtils.isPure(currentMethod)) {
            foundNothing = true;
            specifiedFunctions.add(that.getName().toString());
        }

        if (assignables.size() == 0 && !foundNothing) {
            assignables = assignables.append(M.JmlStoreRefKeyword(JmlTokenKind.BSEVERYTHING));
        }
        return copy;
    }

    public Set<String> getCalledFunctions() {
        calledFunctions.retainAll(specifiedFunctions);
        return calledFunctions;
    }

    public List<Expression> getAssignables() {
        return assignables;
    }

    public void resetAssignables() {
        assignables = new LinkedList<>();
    }
}
