package translation.jml2java;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.jml.clauses.JmlClauseKind;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

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
        //var seq = new ArrayList<>(n.getMembers());
        NodeList<BodyDeclaration<?>> newMembers = new NodeList<>();
        for(BodyDeclaration bd : n.getMembers()) {
            newMembers.add(bd.clone());
        }
        n.setMembers(newMembers);
        //seq.forEach((p) -> {
            //p.accept(this, arg);
        //});
    }

    @Override
    public void visit(MethodDeclaration n, Object arg) {
        if (n.getContracts().isPresent()) {
            var contracts = n.getContracts().get();
            // Only one contract currently supported
            if(contracts.size() == 0) {
                return;
            }
            if (contracts.getFirst().isEmpty() || contracts.size() != 1) {
                throw new IllegalStateException("The number of contracts is " + contracts.size() + " only 1 contract supported for method: " + n.getNameAsString());
            }

            var contract = contracts.getFirst().get();
            if(EmbeddContracts.containsInvalidClauses(contract)) {
                throw new IllegalStateException("Found invalid clause in: " + contract);
            }
            //assert !EmbeddContracts.containsInvalidClauses(contract);

            var ensures = gatherAnd(contract, JmlClauseKind.ENSURES);
            var requires = gatherAnd(contract, JmlClauseKind.REQUIRES);
            var assignable = gather(contract, JmlClauseKind.ASSIGNABLE);

            final var mContract = n.clone();
            mContract.setParentNode(n);
            mContract.setName(n.getNameAsString() + "Contract");
            mContract.addModifier(Modifier.DefaultKeyword.FINAL);
            var body = mContract.getBody().get();
            body.getStatements().clear();

            body.addStatement(Jml2JavaFacade.assert_(requires));
            if (!n.getType().isVoidType()) {
                var returnVarExpr = new VariableDeclarationExpr(n.getType(), RESULTVAR);
                Statement st = new ExpressionStmt(returnVarExpr);
                body.getStatements().add(st);
                body.addStatement(Jml2JavaFacade.havoc(returnVarExpr.asVariableDeclarationExpr()));
            }
            // save references to old variables
            Jml2JavaFacade.storeOlds(ensures).forEach(o -> body.addStatement(o));

            for (Expression expression : assignable) {
                body.addStatement(Jml2JavaFacade.havoc(expression));
            }

            body.addStatement(Jml2JavaFacade.assume(ensures));

            if (!n.getType().isVoidType()) {
                body.addStatement(new ReturnStmt(new NameExpr(RESULTVAR)));
            }

            mContract.addAnnotation(Jml2JavaFacade.createGeneratedAnnotation());

            mContract.getContracts().get().clear();

            last.addMember(mContract);
        }
    }
}
