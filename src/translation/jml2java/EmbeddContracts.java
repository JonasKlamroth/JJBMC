package translation.jml2java;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.clauses.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;

import javax.annotation.Nullable;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (06.05.23)
 */
public class EmbeddContracts extends ModifierVisitor<Object> {
    public static final String RESULTVAR = "__RESULT__";
    private static final Type RETURN_EXCEPTION_TYPE = new ClassOrInterfaceType("ReturnExc");
    private static final String RETURN_EXCEPTION_NAME = "returnExc";

    public static Expression gatherAnd(JmlContract contract, JmlClauseKind jmlClauseKind) {
        var all = gather(contract, jmlClauseKind);
        return all.stream().reduce((a, b) -> new BinaryExpr(a, b, BinaryExpr.Operator.AND)).orElse(
                new BooleanLiteralExpr(true));
    }

    public static List<Expression> gather(JmlContract contract, JmlClauseKind jmlClauseKind) {
        var seq = new LinkedList<Expression>();
        for (JmlClause clause : contract.getClauses()) {
            if (clause.getKind() == jmlClauseKind) {
                if (clause instanceof JmlSimpleExprClause c)
                    seq.add(c.getExpression());
                else if (clause instanceof JmlMultiExprClause c)
                    seq.addAll(c.getExpression());
            }
        }
        return seq;
    }

    public static boolean containsInvalidClauses(JmlContract contract) {
        for (JmlClause clause : contract.getClauses()) {
            switch (clause.getKind()) {
                case ASSIGNABLE, REQUIRES, ENSURES -> {
                }
                default -> {
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public Visitable visit(MethodDeclaration n, Object arg) {
        if (n.getContracts().isPresent() && !Jml2JavaFacade.ignoreNodeByAnnotation(n)) {
            var contracts = n.getContracts().get();
            // Only one conract currently supported
            assert contracts.getFirst().isPresent() && contracts.size() == 1;
            var contract = contracts.getFirst().get();

            assert !containsInvalidClauses(contract);

            var ensures = gatherAnd(contract, JmlClauseKind.ENSURES);
            var requires = gatherAnd(contract, JmlClauseKind.REQUIRES);
            var assignable = gather(contract, JmlClauseKind.ASSIGNABLE);

            contracts.clear();//delete the contract

            n.setBody(constructMethodBody(n, ensures, requires, assignable));

        }
        return super.visit(n, arg);
    }

    private BlockStmt constructMethodBody(MethodDeclaration method,
                                          Expression ensures, Expression requires, List<Expression> assignable) {
        var block = new BlockStmt();
        // assume pre-condition
        block.addStatement(Jml2JavaFacade.assume(ensures));

        if (!method.getType().isVoidType()) {
            // create return value
            block.addStatement(declareVariable(method.getType(), RESULTVAR));
        }

        // save references to old variables
        var oldVariables = Jml2JavaFacade.oldVariables(requires);
        for (Expression oldVariable : oldVariables) {
            var decl = new VariableDeclarator(new VarType(), "old_" + oldVariable.hashCode(), oldVariable);
            block.addStatement(new VariableDeclarationExpr(decl, Modifier.finalModifier()));
        }

        // build try-statement
        Parameter excParam = new Parameter(RETURN_EXCEPTION_TYPE, RETURN_EXCEPTION_NAME);
        var excBody = new BlockStmt();
        block.addStatement(
                new TryStmt((BlockStmt) method.getBody().get().accept(this, null),
                        new NodeList<>(new CatchClause(excParam, excBody)), null));

        //
        block.addStatement(Jml2JavaFacade.assert_(requires));


        if (!method.getType().isVoidType()) {
            // return stored result
            block.addStatement(new ReturnStmt(new NameExpr(RESULTVAR)));
        }
        return block;
    }

    @Override
    public Visitable visit(WhileStmt n, Object arg) {
        if (n.getContracts().isPresent() && n.getContracts().get().size() == 1) {
            var contract = n.getContracts().get().getFirst().get();
            var loopInvar = gatherAnd(contract, JmlClauseKind.LOOP_INVARIANT);
            var assignables = gather(contract, JmlClauseKind.ASSIGNABLE);
            var decreases = gather(contract, JmlClauseKind.DECREASES);

            if (decreases.size() > 1) {
                throw new IllegalStateException("Too many decreases clauses");
            }
            return handleLoop(loopInvar, assignables, decreases.get(0), n.getCondition(), n.getBody());
        }
        return super.visit(n, arg);
    }

    @Override
    public Visitable visit(ForStmt n, Object arg) {
        if (n.getContracts().isPresent() && n.getContracts().get().size() == 1) {
            var outerBlock = new BlockStmt();
            for (Expression init : n.getInitialization()) {
                outerBlock.addStatement(init);
            }
            var body = ensureBlock(n.getBody().clone());
            for (Expression expression : n.getUpdate()) {
                body.addStatement(expression);
            }

            var contract = n.getContracts().get().getFirst().get();
            var loopInvar = gatherAnd(contract, JmlClauseKind.LOOP_INVARIANT);
            var assignables = gather(contract, JmlClauseKind.ASSIGNABLE);
            var decreases = gather(contract, JmlClauseKind.DECREASES);

            if (decreases.size() > 1) {
                throw new IllegalStateException("Too many decreases clauses");
            }
            return handleLoop(loopInvar, assignables, decreases.get(0), n.getCompare().orElse(new BooleanLiteralExpr(true)), body);
        }
        return n;
    }

    public BlockStmt handleLoop(Expression loopInvar, List<Expression> assignables, @Nullable Expression decreases,
                                Expression loopCondition, Statement body) {
        var block = new BlockStmt();
        var oldD = "oldD";
        block.addStatement(Jml2JavaFacade.assert_(loopInvar.clone()));
        for (Expression assignable : assignables) {
            block.addStatement(Jml2JavaFacade.havocForAssignable(assignable));
        }

        var thenBlock = new BlockStmt();
        thenBlock.addStatement((Statement) body.accept(this, null));
        thenBlock.addStatement(Jml2JavaFacade.assert_(loopInvar).clone());
        if (decreases != null) {
            thenBlock.addStatement(Jml2JavaFacade.assertStatement(
                    new BinaryExpr(
                            new BinaryExpr(decreases.clone(), new NameExpr(oldD), BinaryExpr.Operator.LESS),
                            new BinaryExpr(new IntegerLiteralExpr("0"), decreases.clone(), BinaryExpr.Operator.LESS_EQUALS),
                            BinaryExpr.Operator.AND)
            ));
        }
        thenBlock.addStatement(Jml2JavaFacade.assumeStatement(new BooleanLiteralExpr(false)));
        block.addStatement(Jml2JavaFacade.assume(loopInvar).clone());
        block.addStatement(new IfStmt(loopCondition.clone(), thenBlock, null));
        return block;
    }

    private BlockStmt ensureBlock(Statement clone) {
        if (clone instanceof BlockStmt) return (BlockStmt) clone;
        var b = new BlockStmt();
        b.addStatement(clone);
        return b;
    }

    private Expression declareVariable(Type type, String name) {
        return new VariableDeclarationExpr(type, name);
    }
}
