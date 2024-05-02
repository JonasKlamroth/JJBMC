package translation.jml2java;

import cli.CLI;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.clauses.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;

import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (06.05.23)
 */
public class EmbeddContracts extends ModifierVisitor<Object> {

    public static final String RESULTVAR = "__RESULT__";
    private static final Type RETURN_EXCEPTION_TYPE = new ClassOrInterfaceType().setName("ReturnException");
    private static final String RETURN_EXCEPTION_NAME = "returnExc";
    private boolean foundReturn = false;

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
                case ASSIGNABLE, REQUIRES, ENSURES, SIGNALS_ONLY -> {
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
        if (!Jml2JavaFacade.ignoreNodeByAnnotation(n)) {
            var contracts = n.getContracts();
            Expression ensures = new BooleanLiteralExpr(true);
            Expression requires = new BooleanLiteralExpr(true);
            List<Expression> assignable = new ArrayList<>();
            List<Expression> sigOnly = new ArrayList<>();
            // Only one contract currently supported
            if(contracts.size() > 1) {
                return n;
                //throw new UnsupportedException("Only methods with exactly one contract supported for now. Failed for: " + n.getNameAsString());
            }

            if(n.getParentNode().isPresent()) {
                var copy = n.clone();
                ClassOrInterfaceDeclaration parentClass = (ClassOrInterfaceDeclaration) n.getParentNode().get();
                copy.getContracts().clear();
                parentClass.addMember(copy);
            }

            if(contracts.size() != 0) {
                var contract = contracts.getFirst().get();

                assert !containsInvalidClauses(contract);

                ensures = gatherAnd(contract, JmlClauseKind.ENSURES);
                ensures.setParentNode(contract);
                requires = gatherAnd(contract, JmlClauseKind.REQUIRES);
                assignable = gather(contract, JmlClauseKind.ASSIGNABLE);
                sigOnly = gather(contract, JmlClauseKind.SIGNALS_ONLY);
            }

            if(assignable.size() == 0) {
                assignable = Collections.singletonList(new NameExpr("\\everything"));
            }
            contracts.clear();//delete the contract

            n.setBody(constructMethodBody(n, ensures, requires, assignable, sigOnly));
            n.setName(n.getNameAsString() + "Verification");
            n.addAnnotation(Jml2JavaFacade.createGeneratedAnnotation());
        }
        return n;
    }

    private BlockStmt constructMethodBody(MethodDeclaration method,
                                          Expression ensures, Expression requires, List<Expression> assignable, List<Expression> sigOnly) {
        var block = new BlockStmt();
        block.setParentNode(method);
        if (!method.getType().isVoidType()) {
            // create return value
            var returnVarExpr = declareVariable(method.getType(), RESULTVAR);
            Statement st = new ExpressionStmt(returnVarExpr);
            st.setParentNode(method);
            block.getStatements().add(st);
            block.addStatement(Jml2JavaFacade.havoc(returnVarExpr.asVariableDeclarationExpr()));
        }

        // assume pre-condition
        block.addStatement(Jml2JavaFacade.assume(requires));

        // save references to old variables
        Jml2JavaFacade.storeOlds(ensures).forEach(o -> block.addStatement(o));

        foundReturn = false;
        var body = (BlockStmt) method.getBody().get().accept(this, null);

        if(!foundReturn && sigOnly.isEmpty()) {
            block.addStatement(body);
        } else {
            // build try-statement
            var bodyTry = new TryStmt(
                    body,
                    new NodeList<>(), null
            );
            var excBody = new BlockStmt();
            if(foundReturn) {
                Parameter excParam = new Parameter(RETURN_EXCEPTION_TYPE, RETURN_EXCEPTION_NAME);
                CatchClause returnCatchClause = new CatchClause(excParam, excBody);
                bodyTry.getCatchClauses().add(returnCatchClause);
            }
            for (Expression sigOnlyClause : sigOnly) {
                bodyTry.getCatchClauses().add(new CatchClause(
                        new Parameter(new ClassOrInterfaceType().setName(sigOnlyClause.toString()), "exc"),
                        excBody
                ));
            }
            block.addStatement(bodyTry);
        }

        //assert the post-condition
        block.addStatement(Jml2JavaFacade.assert_(ensures));


        if (!method.getType().isVoidType()) {
            // return stored result
            block.addStatement(new ReturnStmt(new NameExpr(RESULTVAR)));
        }
        return block;
    }

    @Override
    public Visitable visit(WhileStmt n, Object arg) {
        if (n.getContracts().size() == 1) {
            var contract = n.getContracts().getFirst().get();
            var loopInvar = gather(contract, JmlClauseKind.LOOP_INVARIANT);
            var assignables = gather(contract, JmlClauseKind.ASSIGNABLE);
            var decreases = gather(contract, JmlClauseKind.DECREASES);

            if (decreases.size() != 1) {
                throw new IllegalStateException("Only exactly one decreases clause supported. However found " +
                        decreases.size() + " in " + n.getContracts());
            }
            return handleLoop(loopInvar, assignables, decreases.get(0), n.getCondition(), n.getBody(), new NodeList<>(), n);
        }
        return super.visit(n, arg);
    }

    @Override
    public Visitable visit(ForStmt n, Object arg) {
        if (n.getContracts().size() == 1) {

            var body = ensureBlock(n.getBody().clone());
            body.setParentNode(n);
            for (Expression expression : n.getUpdate()) {
                body.addStatement(expression);
            }

            var contract = n.getContracts().getFirst().get();
            var loopInvar = gather(contract, JmlClauseKind.LOOP_INVARIANT);
            var assignables = gather(contract, JmlClauseKind.ASSIGNABLE);
            var decreases = gather(contract, JmlClauseKind.DECREASES);

            if (decreases.size() > 1) {
                throw new IllegalStateException("Too many decreases clauses");
            }
            var res = handleLoop(loopInvar, assignables, decreases.get(0), n.getCompare().orElse(new BooleanLiteralExpr(true)), body, n.getInitialization(), n);
            res.setParentNode(n);
            return res;
        }
        return n;
    }

    public BlockStmt handleLoop(List<Expression> loopInvars, List<Expression> assignables, @Nullable Expression decreases,
                                Expression loopCondition, Statement body, List<Expression> inits, Node parent) {
        var block = new BlockStmt();
        block.setParentNode(parent);
        for(Expression e : inits) {
            block.addStatement(new ExpressionStmt(e));
        }
        var oldD = "oldD" + Jml2JavaExpressionTranslator.counter.getAndIncrement();
        block.addStatement(
                new VariableDeclarationExpr(
                        new VariableDeclarator(
                                new PrimitiveType(PrimitiveType.Primitive.INT),
                                oldD,
                                decreases.clone())));

        for(Expression loopInvar : loopInvars) {
            block.addStatement(Jml2JavaFacade.assert_(loopInvar.clone()));
        }
        for (Expression assignable : assignables) {
            block.addStatement(Jml2JavaFacade.havoc(assignable));
        }

        var thenBlock = new BlockStmt();
        var ifThen = new IfStmt(loopCondition.clone(), thenBlock, null);
        ifThen.setParentNode(block);
        thenBlock.addStatement((Statement) body.accept(this, null));
        for(Expression loopInvar : loopInvars) {
            thenBlock.addStatement(Jml2JavaFacade.assert_(loopInvar).clone());
        }
        if (decreases != null) {
            thenBlock.addStatement(Jml2JavaFacade.assertStatement(
                    new BinaryExpr(
                            new BinaryExpr(decreases.clone(), new NameExpr(oldD), BinaryExpr.Operator.LESS),
                            new BinaryExpr(new IntegerLiteralExpr("0"), decreases.clone(), BinaryExpr.Operator.LESS_EQUALS),
                            BinaryExpr.Operator.AND)
            ));
        }
        thenBlock.addStatement(Jml2JavaFacade.assumeStatement(new BooleanLiteralExpr(false)));
        for(Expression loopInvar : loopInvars) {
            block.addStatement(Jml2JavaFacade.assume(loopInvar).clone());
        }
        block.addStatement(ifThen);
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

    @Override
    public Visitable visit(MethodCallExpr n, Object arg) {
        if(CLI.forceInliningMethods) {
            return super.visit(n, arg);
        }
        var arguments = new ArrayList<Expression>();
        for(Expression argument : n.getArguments()) {
            arguments.add((Expression) argument.accept(this, arg));
        }
        var contractCall = new MethodCallExpr(n.getName().toString() + "Contract", n.getArguments().toArray(Expression[]::new));
        return contractCall;
    }

    @Override
    public Visitable visit(ReturnStmt n, Object arg) {
        foundReturn = true;
        BlockStmt block = new BlockStmt();
        block.setParentNode(n.getParentNodeForChildren());
        if (n.getExpression().isPresent()) {
            Expression returnVal = (Expression) n.getExpression().get().accept(this, arg);
            block.addStatement(new AssignExpr(new NameExpr(RESULTVAR), returnVal, AssignExpr.Operator.ASSIGN));
        }
        block.addStatement(new ThrowStmt(new ObjectCreationExpr(null, new ClassOrInterfaceType().setName(RETURN_EXCEPTION_TYPE.asString()), new NodeList<>())));
        return block;
    }
}
