package translation.jml2java;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.jml.clauses.JmlClauseKind;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import java.util.ArrayList;

import static translation.jml2java.EmbeddContracts.*;

/**
 * @author Alexander Weigl
 * @version 1 (06.05.23)
 */
public class CreateMethodContracts extends VoidVisitorAdapter<Object> {
    TypeDeclaration<?> last;

    @Override
    public void visit(ClassOrInterfaceDeclaration n, Object arg) {
        last = n;

        // Make a copy to avoid concurrent modification exception as new methods are created
        var seq = new ArrayList<>(n.getMembers());
        seq.forEach((p) -> {
            p.accept(this, arg);
        });
    }

    @Override
    public void visit(MethodDeclaration n, Object arg) {
        if (n.getContracts().isPresent()) {
            var contracts = n.getContracts().get();
            // Only one conract currently supported
            if (contracts.getFirst().isEmpty() || contracts.size() != 1) {
                throw new IllegalStateException("The number of contracts is " + contracts.size() + " only 1 contract supported.");
            }

            var contract = contracts.getFirst().get();
            assert !EmbeddContracts.containsInvalidClauses(contract);

            var ensures = gatherAnd(contract, JmlClauseKind.ENSURES);
            var requires = gatherAnd(contract, JmlClauseKind.REQUIRES);
            var assignable = gather(contract, JmlClauseKind.ASSIGNABLE);

            final var mContract = n.clone();
            mContract.setName(n.getNameAsString() + "Contract");
            mContract.addModifier(Modifier.DefaultKeyword.FINAL);
            var body = mContract.getBody().get();
            body.getStatements().clear();

            body.addStatement(Jml2JavaFacade.assert_(ensures));
            body.addStatement(new VariableDeclarationExpr(mContract.getType().clone(), RESULTVAR));
            // save references to old variables
            var oldVariables = Jml2JavaFacade.oldVariables(requires);
            for (Expression oldVariable : oldVariables) {
                var decl = new VariableDeclarator(new VarType(), "old_" + oldVariable.hashCode(), oldVariable);
                body.addStatement(new VariableDeclarationExpr(decl, Modifier.finalModifier()));
            }

            for (Expression expression : assignable) {
                body.addStatement(Jml2JavaFacade.havocForAssignable(expression));
            }

            body.addStatement(Jml2JavaFacade.assume(requires));

            body.addStatement(new ReturnStmt(new NameExpr(RESULTVAR)));

            mContract.addAnnotation(Jml2JavaFacade.createGeneratedAnnotation());

            mContract.getContracts().get().clear();

            last.addMember(mContract);
        }
    }
}
