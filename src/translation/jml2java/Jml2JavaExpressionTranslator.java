package translation.jml2java;

import cli.CLI;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import translation.jml2java.Jml2JavaFacade.Result;

import java.util.concurrent.atomic.AtomicInteger;

import static translation.jml2java.Jml2JavaFacade.resolvedType2Type;
import static translation.jml2java.Jml2JavaFacade.unroll;

/**
 * Translates JML expressions into a bunch of Java statements and a final expression.
 *
 * @author Alexander Weigl
 * @version 1 (04.10.22)
 */
public class Jml2JavaExpressionTranslator {
    public static final AtomicInteger counter = new AtomicInteger();

    public Result accept(Expression e, TranslationMode arg) {
        if (Jml2JavaFacade.containsJmlExpression(e)) {
            return e.accept(new Jml2JavaVisitor(), arg);
        }
        return new Result(e);
    }

    private Statement createAssignmentFor(Expression e) {
        var decl = new VariableDeclarationExpr(
                new VariableDeclarator(new VarType(),
                        newTargetForAssignment(), e));
        decl.addModifier(Modifier.DefaultKeyword.FINAL);
        return new ExpressionStmt(decl);
    }

    private SimpleName getTargetForAssignment() {
        return new SimpleName("_gen_" + counter.get());
    }

    private SimpleName newTargetForAssignment() {
        counter.getAndIncrement();
        return getTargetForAssignment();
    }

    public Expression findPredicate(JmlQuantifiedExpr n) {
        return n.getExpressions().get(n.getExpressions().size() - 1);
    }

    public static Expression findBound(JmlQuantifiedExpr n) {
        if (n.getExpressions().size() == 2)
            return n.getExpressions().get(0);
        else if (n.getExpressions().size() == 1)
            if (n.getExpressions().get(0) instanceof BinaryExpr be)
                return be.getLeft();
        throw new IllegalArgumentException("Could not determine bound.");

    }

    private final class Jml2JavaVisitor extends GenericVisitorAdapter<Result, TranslationMode> {
        QuantifierSplitter quantifierSplitter = new QuantifierSplitter();

        @Override
        public Result visit(ConditionalExpr n, TranslationMode arg) {

            return super.visit(n, arg);
        }

        @Override
        public Result visit(JmlQuantifiedExpr n, TranslationMode arg) {
            if (n.getBinder() == JmlQuantifiedExpr.JmlDefaultBinder.FORALL)
                return arg == TranslationMode.ASSERT ? visitForall(n, arg) : visitForallLoop(n, arg);
            if (n.getBinder() == JmlQuantifiedExpr.JmlDefaultBinder.EXISTS)
                return arg == TranslationMode.ASSUME ? visitExists(n, arg) : visitExistsLoop(n, arg);

            throw new IllegalArgumentException("Unsupported quantifier " + n.getBinder());
        }

        /**
         * Translate a universal quantification into a for loop over the range
         */
        private Result visitForallLoop(JmlQuantifiedExpr n, TranslationMode arg) {
            final var b = new BlockStmt();
            b.setParentNode(n.getParentNodeForChildren());
            final var boolVar = "b" + counter.getAndIncrement();
            //final var loopVar = "i" + counter.getAndIncrement();
            final var loopVar = n.getVariables().get(0).getNameAsString();

            var lowerBoundRes = quantifierSplitter.getLowerBound(n).accept(this, arg);
            var upperBoundRes = quantifierSplitter.getUpperBound(n).accept(this, arg);
            var lowerBound = lowerBoundRes.value;
            var upperBound = upperBoundRes.value;
            b.getStatements().addAll(lowerBoundRes.getStatements());
            b.getStatements().addAll(upperBoundRes.getStatements());

            // add: boolean bN = true
            NodeList<Statement> varDefs = new NodeList<>(new ExpressionStmt(
                    new VariableDeclarationExpr(
                            new VariableDeclarator(
                                    new PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
                                    boolVar,
                                    new BooleanLiteralExpr(true)))));

            //
            var init = new VariableDeclarationExpr(
                    new VariableDeclarator(
                            new PrimitiveType(PrimitiveType.Primitive.INT),
                            loopVar, lowerBound));
            var compare = new BinaryExpr(new NameExpr(loopVar), upperBound, BinaryExpr.Operator.LESS);
            var update = new UnaryExpr(new NameExpr(loopVar), UnaryExpr.Operator.PREFIX_INCREMENT);
            BlockStmt forBody = new BlockStmt();

            var clone = n.getExpressions().getLast().get().clone();
            var res = clone.accept(this, arg);
            res.value = (Expression) res.value.accept(new ReplaceVariable(n.getVariables().get(0), init.getVariable(0).getNameAsString()), null);
            forBody.getStatements().addAll(res.statements);
            varDefs.addAll(res.necessaryVars);

            // boolVar = (boolVar && val)
            forBody.addStatement(
                    new AssignExpr(new NameExpr(boolVar),
                            new EnclosedExpr(
                                    new BinaryExpr(new NameExpr(boolVar), res.value, BinaryExpr.Operator.AND)),
                            AssignExpr.Operator.ASSIGN));


            b.addStatement(new ForStmt(new NodeList<>(init), compare, new NodeList<>(update), forBody));
            return new Result(b.getStatements(), new NameExpr(boolVar), varDefs);
        }


        /**
         * Translate a universal quantification into a for loop over the range
         */
        private Result visitExistsLoop(JmlQuantifiedExpr n, TranslationMode arg) {
            final var b = new BlockStmt();
            b.setParentNode(n.getParentNodeForChildren());
            final var boolVar = "b" + counter.getAndIncrement();
            final var loopVar = "i" + counter.getAndIncrement();

            var lowerBound = quantifierSplitter.getLowerBound(n);
            var upperBound = quantifierSplitter.getUpperBound(n);


            // add: boolean bN = false
            NodeList<Statement> varDefs = new NodeList<>(new ExpressionStmt(
                    new VariableDeclarationExpr(
                            new VariableDeclarator(
                                    new PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
                                    boolVar,
                                    new BooleanLiteralExpr(false)))));

            //
            var init = new VariableDeclarationExpr(
                    new VariableDeclarator(
                            new PrimitiveType(PrimitiveType.Primitive.INT),
                            loopVar, lowerBound));
            var compare = new BinaryExpr(new NameExpr(loopVar), upperBound, BinaryExpr.Operator.LESS);
            var update = new UnaryExpr(new NameExpr(loopVar), UnaryExpr.Operator.PREFIX_INCREMENT);
            BlockStmt forBody = new BlockStmt();


            var clone = n.getExpressions().getLast().get().clone();
            var res = clone.accept(this, arg);
            forBody.getStatements().addAll(res.statements);
            res.value = (Expression) res.value.accept(new ReplaceVariable(n.getVariables().get(0), init.getVariable(0).getNameAsString()), null);
            varDefs.addAll(res.necessaryVars);


            // boolVar = (boolVar || val)
            forBody.addStatement(
                    new AssignExpr(new NameExpr(boolVar),
                            new EnclosedExpr(
                                    new BinaryExpr(new NameExpr(boolVar), res.value, BinaryExpr.Operator.OR)),
                            AssignExpr.Operator.ASSIGN));


            b.addStatement(new ForStmt(new NodeList<>(init), compare, new NodeList<>(update), forBody));
            return new Result(b.getStatements(), new NameExpr(boolVar), varDefs);
        }


        private Result visitForall(JmlQuantifiedExpr n, TranslationMode arg) {
            n = n.clone();
            var para = quantifierSplitter.getVariable(n);
            var s = assignNondet(para);
            var newExpr = new BinaryExpr(
                    new EnclosedExpr(n.getExpressions().get(0)),
                    new EnclosedExpr(n.getExpressions().get(1)),
                    BinaryExpr.Operator.IMPLICATION)
                    .setParentNode(n)
                    .accept(this, arg);
            newExpr.statements.addFirst(s);
            return newExpr;
        }

        private String newSymbol(String prefix) {
            return prefix + counter.getAndIncrement();
        }

        private Result visitExists(JmlQuantifiedExpr n, TranslationMode arg) {
            var para = quantifierSplitter.getVariable(n);
            //var lowerBoundO = quantifierSplitter.getLowerBound(n);
            //var upperBoundO= quantifierSplitter.getUpperBound(n);
            var s = assignNondet(para);
            var newExpr = new BinaryExpr(
                    n.getExpressions().get(0),
                    n.getExpressions().get(1),
                    BinaryExpr.Operator.AND)
                    .accept(this, arg);
            newExpr.statements.addFirst(s);
            return newExpr;
        }

        private Statement assignNondet(Parameter para) {
            return new ExpressionStmt(
                    new VariableDeclarationExpr(
                            new VariableDeclarator(para.getType(), para.getNameAsString(),
                                    new MethodCallExpr("CProver.nondetInt")
                            )));
        }


        /**
         * <code><pre>
         *     (\let x = expr1; expr2)
         * </pre></code>
         *
         * <code><pre>
         * { var new; { val(expr1); x = v; eval(expr2); new = v; ) } ; new
         * </pre></code>
         * * @param n
         *
         * @param arg
         * @return
         */
        @Override
        public Result visit(JmlLetExpr n, TranslationMode arg) {
            var inner = new BlockStmt();
            var outer = new BlockStmt();

            SimpleName target = newTargetForAssignment();
            var type = n.getBody().calculateResolvedType();
            outer.addAndGetStatement(
                    new ExpressionStmt(new VariableDeclarationExpr(resolvedType2Type(type),
                            target.asString())));
            outer.addStatement(inner);

            for (VariableDeclarator variable : n.getVariables().getVariables()) {
                var v = accept(variable.getInitializer().get(), arg);
                inner.getStatements().addAll(v.statements);
                inner.addAndGetStatement(
                        declareAndAssign(variable, v.value));
            }
            var body = accept(n.getBody(), arg);
            inner.getStatements().addAll(body.statements);
            inner.addAndGetStatement(new AssignExpr(new NameExpr(target.asString()),
                    body.value, AssignExpr.Operator.ASSIGN));
            return new Result(outer.getStatements(), new NameExpr(target.asString()));
        }

        private Statement declareAndAssign(VariableDeclarator variable, Expression value) {
            return new ExpressionStmt(new VariableDeclarationExpr(
                    new VariableDeclarator(variable.getType(), variable.getName(), value)
            ));
        }

        @Override
        public Result visit(BinaryExpr n, TranslationMode arg) {
            var left = accept(n.getLeft(), arg);
            var right = accept(n.getRight(), arg);
            var res =  switch (n.getOperator()) {
                case AND -> combine(left.statements,
                        ifThen(left.value, right.statements),
                        new BinaryExpr(left.value, right.value, BinaryExpr.Operator.AND));
                case OR -> combine(left.statements,
                        ifThen(negate(left.value), right.statements),
                        new BinaryExpr(left.value, right.value, BinaryExpr.Operator.OR));
                case IMPLICATION -> combine(left.statements,
                        ifThen(left.value, right.statements),
                        new BinaryExpr(negate(left.value), right.value, BinaryExpr.Operator.OR));
                case RIMPLICATION -> combine(right.statements,
                        ifThen(right.value, left.statements),
                        new BinaryExpr(negate(right.value), left.value, BinaryExpr.Operator.OR));
                case EQUIVALENCE -> combine(left, right,
                        new BinaryExpr(left.value, right.getValue(), BinaryExpr.Operator.EQUALS));
                case SUBTYPE, SUB_LOCK, SUB_LOCKE -> throw new IllegalArgumentException("Unsupported operators.");
                default -> combine(left, right,
                        new BinaryExpr(left.value, right.getValue(), n.getOperator()));
            };
            res.necessaryVars = left.necessaryVars;
            res.necessaryVars.addAll(right.necessaryVars);
            return res;
        }

        private Result combine(Result left, Result right, BinaryExpr expr) {
            var n = new NodeList<>(left.statements);
            n.addAll(right.statements);
            var n1 = new NodeList<>(left.necessaryVars);
            n1.addAll(right.necessaryVars);
            return new Result(n, expr, n1);
        }

        private Expression negate(Expression value) {
            return new UnaryExpr(value, UnaryExpr.Operator.LOGICAL_COMPLEMENT);
        }

        private Result combine(NodeList<Statement> before, Statement combination, BinaryExpr expr) {
            var n = new NodeList<>(before);
            n.add(combination);
            return new Result(n, expr);
        }

        private IfStmt ifThen(Expression value, NodeList<Statement> statements) {
            return new IfStmt(value, new BlockStmt(statements), null);
        }


        @Override
        public Result visit(ArrayAccessExpr n, TranslationMode arg) {
            var name = n.getName().accept(this, arg);
            var index = n.getIndex().accept(this, arg);
            name.statements.addAll(index.statements);
            return new Result(name.statements, new ArrayAccessExpr(name.getValue(), index.value), name.necessaryVars);
        }

        @Override
        public Result visit(ArrayCreationExpr n, TranslationMode arg) {
            return super.visit(n, arg);
        }

        @Override
        public Result visit(ArrayInitializerExpr n, TranslationMode arg) {
            return super.visit(n, arg);
        }

        @Override
        public Result visit(AssignExpr n, TranslationMode arg) {
            throw new IllegalStateException("Assignments are forbidden in JML.");
        }

        @Override
        public Result visit(ClassExpr n, TranslationMode arg) {
            throw new IllegalStateException("Assignments are forbidden in JML.");
        }

        @Override
        public Result visit(BooleanLiteralExpr n, TranslationMode arg) {
            return new Result(n);
        }

        @Override
        public Result visit(CastExpr n, TranslationMode arg) {
            var inner = n.getExpression().accept(this, arg);
            return new Result(inner.statements,
                    new CastExpr(n.getType(), inner.value), inner.necessaryVars);
        }

        @Override
        public Result visit(CharLiteralExpr n, TranslationMode arg) {
            return new Result(n);
        }

        @Override
        public Result visit(DoubleLiteralExpr n, TranslationMode arg) {
            return new Result(n);
        }

        @Override
        public Result visit(EnclosedExpr n, TranslationMode arg) {
            var inner = n.getInner().accept(this, arg);
            return new Result(inner.statements, new EnclosedExpr(inner.value), inner.necessaryVars);
        }

        @Override
        public Result visit(FieldAccessExpr n, TranslationMode arg) {
            var inner = n.getScope().accept(this, arg);
            return new Result(inner.statements,
                    new FieldAccessExpr(inner.getValue(), n.getTypeArguments().orElse(null),
                            new SimpleName(n.getNameAsString())), inner.necessaryVars);
        }

        @Override
        public Result visit(InstanceOfExpr n, TranslationMode arg) {
            var inner = n.getExpression().accept(this, arg);
            return new Result(inner.statements,
                    new InstanceOfExpr(inner.value, n.getType()), inner.necessaryVars);
        }

        @Override
        public Result visit(IntegerLiteralExpr n, TranslationMode arg) {
            return new Result(n);
        }

        @Override
        public Result visit(LongLiteralExpr n, TranslationMode arg) {
            return new Result(n);
        }

        @Override
        public Result visit(MarkerAnnotationExpr n, TranslationMode arg) {
            return super.visit(n, arg);
        }

        @Override
        public Result visit(MethodCallExpr n, TranslationMode arg) {
            if (n.getNameAsString().equals("\\old")) {
                Expression expr = new NameExpr("old_" + Math.abs(n.getArgument(0).hashCode()));
                var relevantQuantifiers = Jml2JavaFacade.getRelevantQuantifiers(n.getArgument(0));
                for(JmlQuantifiedExpr q : relevantQuantifiers) {
                    expr = new ArrayAccessExpr(expr,
                            new BinaryExpr(QuantifierSplitter.getVariable(q).getNameAsExpression(),
                                    new IntegerLiteralExpr(String.valueOf(CLI.maxArraySize)),
                                    BinaryExpr.Operator.REMAINDER));
                }
                return new Result(expr);
            }

            Expression scope = null;
            NodeList<Statement> statements = new NodeList<>();

            if (n.getScope().isPresent()) {
                var s = n.getScope().get().accept(this, arg);
                scope = s.value;
                statements.addAll(s.statements);
            }

            var args = new NodeList<Expression>();
            for (Expression argument : n.getArguments()) {
                var a = argument.accept(this, arg);
                statements.addAll(a.statements);
                args.add(a.value);
            }
            return new Result(statements,
                    new MethodCallExpr(scope,
                            n.getTypeArguments().orElse(null),
                            n.getNameAsString(), args));
        }

        @Override
        public Result visit(NameExpr n, TranslationMode arg) {
            if(n.getName().toString().equals("\\result")) {
                return new Result(new NameExpr(EmbeddContracts.RESULTVAR));
            }
            return new Result(n);
        }

        @Override
        public Result visit(NullLiteralExpr n, TranslationMode arg) {
            return new Result(n);
        }

        @Override
        public Result visit(ObjectCreationExpr n, TranslationMode arg) {
            throw new IllegalStateException("Object creation not allowed");
        }

        @Override
        public Result visit(SingleMemberAnnotationExpr n, TranslationMode arg) {
            throw new IllegalStateException("Object creation not allowed");
        }

        @Override
        public Result visit(StringLiteralExpr n, TranslationMode arg) {
            return new Result(n);
        }

        @Override
        public Result visit(SuperExpr n, TranslationMode arg) {
            return new Result(n);
        }

        @Override
        public Result visit(ThisExpr n, TranslationMode arg) {
            return new Result(n);
        }

        @Override
        public Result visit(UnaryExpr n, TranslationMode arg) {
            var inner = n.getExpression().accept(this, arg.switchPolarity());
            return new Result(inner.statements,
                    new UnaryExpr(inner.value, n.getOperator()), inner.necessaryVars);
        }

        @Override
        public Result visit(VariableDeclarationExpr n, TranslationMode arg) {
            throw new IllegalStateException("Object creation not allowed");
        }

        @Override
        public Result visit(LambdaExpr n, TranslationMode arg) {
            throw new IllegalStateException("Object creation not allowed");
        }

        @Override
        public Result visit(MethodReferenceExpr n, TranslationMode arg) {
            throw new IllegalStateException("Object creation not allowed");
        }

        @Override
        public Result visit(TypeExpr n, TranslationMode arg) {
            throw new IllegalStateException("Object creation not allowed");
        }

        @Override
        public Result visit(SwitchExpr n, TranslationMode arg) {
            throw new IllegalStateException("SwitchExpr not allowed");
        }

        @Override
        public Result visit(TextBlockLiteralExpr n, TranslationMode arg) {
            return new Result(n);
        }

        @Override
        public Result visit(PatternExpr n, TranslationMode arg) {
            return new Result(n);
        }

        @Override
        public Result visit(JmlLabelExpr n, TranslationMode arg) {
            var inner = n.getExpression().accept(this, arg);
            //TODO weigl maybe assign a name to the expression
            return inner;
        }

        @Override
        public Result visit(JmlMultiCompareExpr n, TranslationMode arg) {
            return unroll(n).accept(this, arg);
        }

        @Override
        public Result visit(JmlBinaryInfixExpr n, TranslationMode arg) {
            throw new IllegalStateException("not allowed");
        }
    }


}
