package jjbmc.jml2java;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.jml.clauses.JmlClauseKind;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import jjbmc.JJBMCOptions;
import lombok.RequiredArgsConstructor;
import org.jspecify.annotations.Nullable;

import static jjbmc.jml2java.EmbeddContracts.*;

/**
 * @author Alexander Weigl
 * @version 1 (06.05.23)
 */
@RequiredArgsConstructor
public class CreateMethodContracts extends VoidVisitorAdapter<@Nullable Object> {
    @Nullable TypeDeclaration<?> last;
    private final int maxArraySize;

    public CreateMethodContracts(JJBMCOptions options) {
        this(options.getMaxArraySize());
    }


    @Override
    public void visit(ClassOrInterfaceDeclaration n, Object arg) {
        last = n;

        // Make a copy to avoid concurrent modification exception as new methods are created
        //var seq = new ArrayList<>(n.getMembers());
        NodeList<BodyDeclaration<?>> newMembers = new NodeList<>();
        for (BodyDeclaration bd : n.getMembers()) {
            newMembers.add(bd.clone());
        }
        n.setMembers(newMembers);
        //seq.forEach((p) -> {
        //p.accept(this, arg);
        //});
    }

    @Override
    public void visit(MethodDeclaration n, Object arg) {
        var contracts = n.getContracts();
        // Only one contract currently supported
        if (contracts.isEmpty()) {
            return;
        }
        if (contracts.getFirst().isEmpty() || contracts.size() != 1) {
            throw new IllegalStateException("The number of contracts is " + contracts.size() + " only 1 contract supported for method: " + n.getNameAsString());
        }

        var contract = contracts.getFirst().get();
        if (EmbeddContracts.containsInvalidClauses(contract)) {
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
        Jml2JavaFacade.storeOlds(ensures, maxArraySize).forEach(body::addStatement);

        for (Expression expression : assignable) {
            body.addStatement(Jml2JavaFacade.havoc(expression));
        }

        body.addStatement(Jml2JavaFacade.assume(ensures));

        if (!n.getType().isVoidType()) {
            body.addStatement(new ReturnStmt(new NameExpr(RESULTVAR)));
        }

        mContract.addAnnotation(Jml2JavaFacade.createGeneratedAnnotation());

        mContract.getContracts().clear();

        last.addMember(mContract);
    }
}
