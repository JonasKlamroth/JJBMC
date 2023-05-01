package translation.jml2java;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.expr.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import translation.jml2java.Jml2JavaFacade.Result;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * Translates JML expressions into a bunch of Java statements and a final expression.
 *
 * @author Alexander Weigl
 * @version 1 (04.10.22)
 */
public class Jml2JavaExpressionTranslator {
    private final AtomicInteger counter = new AtomicInteger();

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
                return visitForall(n, arg);
            if (n.getBinder() == JmlQuantifiedExpr.JmlDefaultBinder.EXISTS)
                return visitExists(n, arg);

            throw new IllegalArgumentException("Unsupport quantifier " + n.getBinder());
        }

        private Result visitForall(JmlQuantifiedExpr n, TranslationMode arg) {
            var para = quantifierSplitter.getVariable(n);
            var s = assignNondet(para);
            var newExpr = new BinaryExpr(
                    n.getExpressions().get(0),
                    n.getExpressions().get(1),
                    BinaryExpr.Operator.IMPLICATION)
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
                                    new MethodCallExpr("nondet_int")
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
            var outer = new BlockStmt(new NodeList<>(inner));

            SimpleName target = newTargetForAssignment();
            var type = n.getBody().calculateResolvedType();
            outer.addAndGetStatement(
                    new ExpressionStmt(new VariableDeclarationExpr(resolvedType2Type(type),
                            target.asString())));

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
            return switch (n.getOperator()) {
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
        }

        private Result combine(Result left, Result right, BinaryExpr expr) {
            var n = new NodeList<>(left.statements);
            n.addAll(right.statements);
            return new Result(n, expr);
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
            return super.visit(n, arg);
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
                    new CastExpr(n.getType(), inner.value));
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
            return new Result(inner.statements, new EnclosedExpr(inner.value));
        }

        @Override
        public Result visit(FieldAccessExpr n, TranslationMode arg) {
            var inner = n.getScope().accept(this, arg);
            return new Result(inner.statements,
                    new FieldAccessExpr(inner.getValue(), n.getTypeArguments().orElse(null),
                            new SimpleName(n.getNameAsString())));
        }

        @Override
        public Result visit(InstanceOfExpr n, TranslationMode arg) {
            var inner = n.getExpression().accept(this, arg);
            return new Result(inner.statements,
                    new InstanceOfExpr(inner.value, n.getType()));
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
            var inner = n.getExpression().accept(this, arg);
            return new Result(inner.statements,
                    new UnaryExpr(inner.value, n.getOperator()));
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

    public static Expression unroll(JmlMultiCompareExpr n) {
        Expression r;
        if (n.getExpressions().isEmpty()) {
            r = new BooleanLiteralExpr(true);
        } else if (n.getExpressions().size() == 1) {
            r = n.getExpressions().get(0);
        } else {
            Expression e = null;
            for (int i = 0; i < n.getExpressions().size() - 1; i++) {
                BinaryExpr cmp = new BinaryExpr(
                        n.getExpressions().get(i).clone(),
                        n.getExpressions().get(i + 1).clone(),
                        n.getOperators().get(i));
                e = e == null ? cmp : new BinaryExpr(e, cmp, BinaryExpr.Operator.AND);
            }
            r = e;
        }
        r.setParentNode(n.getParentNode().orElse(null));
        return r;
    }

    public static Type resolvedType2Type(ResolvedType type) {
        if (type.isPrimitive()) {
            ResolvedPrimitiveType rType = type.asPrimitive();
            return new PrimitiveType(
                    switch (rType) {
                        case BYTE -> PrimitiveType.Primitive.BYTE;
                        case SHORT -> PrimitiveType.Primitive.SHORT;
                        case CHAR -> PrimitiveType.Primitive.CHAR;
                        case INT -> PrimitiveType.Primitive.INT;
                        case LONG -> PrimitiveType.Primitive.LONG;
                        case BOOLEAN -> PrimitiveType.Primitive.BOOLEAN;
                        case FLOAT -> PrimitiveType.Primitive.FLOAT;
                        case DOUBLE -> PrimitiveType.Primitive.DOUBLE;
                    }
            );
        }

        if (type.isArray()) {
            ResolvedArrayType aType = type.asArrayType();
            return new ArrayType(resolvedType2Type(aType.getComponentType()));
        }

        if (type.isReferenceType()) {
            var rType = type.asReferenceType();
            return new ClassOrInterfaceType(rType.getQualifiedName());
        }

        throw new RuntimeException("Unsupported type");
    }

}
