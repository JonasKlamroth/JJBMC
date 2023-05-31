package translation.jml2java;

import cli.MyPPrintVisitor;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.expr.JmlMultiCompareExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NonNull;
import org.jetbrains.annotations.NotNull;

import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Stack;

/**
 * Transformation of JML expressions into equivalent Java code.
 *
 * @author Alexander Weigl
 * @version 1 (04.10.22)
 */
public class Jml2JavaFacade {
    public static Statement assumeStatement(Expression e) {
        return new ExpressionStmt(new MethodCallExpr(new NameExpr("CProver"), "assume", new NodeList<>(e)));
    }

    public static Statement assertStatement(Expression e) {
        return new ExpressionStmt(new MethodCallExpr(new NameExpr("CProver"), "assert", new NodeList<>(e)));
    }

    public static Statement assume(Expression ensures) {
        var r = translate(ensures, TranslationMode.ASSUME);
        r.statements.add(assumeStatement(r.value));
        return new BlockStmt(r.statements);
    }

    public static BlockStmt assert_(Expression requires) {
        var r = translate(requires, TranslationMode.ASSUME);
        r.statements.add(assertStatement(r.value));
        return new BlockStmt(r.statements);
    }

    // Returns a list of expression under "\old"
    public static List<Expression> oldVariables(Expression requires) {
        var seq = new LinkedList<Expression>();
        requires.walk(MethodCallExpr.class, i -> {
            if (i.getNameAsString().equals("\\old")) {
                seq.add(i.getArgument(0));
            }
        });

        return seq;
    }

    public static Statement havocForAssignable(Expression expression) {
        return new ExpressionStmt(new MethodCallExpr(new NameExpr("CProver"), "havoc", new NodeList<>(expression)));
    }

    public static CompilationUnit translate(CompilationUnit cu) {
        // add exception type to the compiluation unit
        cu.addType(Jml2JavaFacade.createExceptionClass());

        //add method stubs for call to contracts
        cu.accept(new CreateMethodContracts(), null);

        //rewrite methods and loops
        return (CompilationUnit) cu.accept(new EmbeddContracts(), null);
    }

    public static AnnotationExpr createGeneratedAnnotation() {
        return new SingleMemberAnnotationExpr(
                new Name("javax.annotation.processing.Generated"),
                new StringLiteralExpr("JJBMC")
        );
    }


    @Data
    @AllArgsConstructor
    static class Result {
        @NonNull
        NodeList<Statement> statements = new NodeList<>();
        @NonNull
        Expression value;

        public Result(@NonNull Expression e) {
            this.value = e;
        }
    }

    /**
     * Fixes an error in JavaParser pretty printing of JML-contracts
     *
     * @param translation
     * @return
     */
    @NotNull
    public static String pprint(@NotNull Node translation) {
        DefaultPrettyPrinter pp = new DefaultPrettyPrinter(
                MyPPrintVisitor::new, new DefaultPrinterConfiguration());
        return pp.print(translation);
    }


    @NotNull
    public static ClassOrInterfaceDeclaration createExceptionClass() {
        var exceptionClass = new ClassOrInterfaceDeclaration();
        //exceptionClass.addModifier(Modifier.DefaultKeyword.PUBLIC, Modifier.DefaultKeyword.STATIC);
        exceptionClass.setName("ReturnException");
        exceptionClass.setExtendedTypes(new NodeList<>(new ClassOrInterfaceType("Exception")));
        exceptionClass.addSingleMemberAnnotation("javax.annotation.processing.Generated", "\"JJBMC\"");
        return exceptionClass;
    }

    /**
     * Checks whether the given node is annotated by {@code @javax.annotation.processing.Generated("JJBMC")}
     *
     * @param node
     * @return
     */
    public static boolean ignoreNodeByAnnotation(NodeWithAnnotations<?> node) {
        try {
            var annotation = node.getAnnotationByName("javax.annotation.processing.Generated");
            if (annotation.isPresent()) {
                var value = annotation.get().asSingleMemberAnnotationExpr().getMemberValue()
                        .asStringLiteralExpr().getValue();
                return value.equals("JJBMC");
            }
        } catch (NoSuchElementException | ClassCastException | IllegalStateException ignored) {
        }
        return false;
    }

    public static Result translate(Expression expression, TranslationMode mode) {
        Jml2JavaExpressionTranslator j2jt = new Jml2JavaExpressionTranslator();
        return j2jt.accept(expression, mode);
    }


    public static boolean containsJmlExpression(Expression expression) {
        Stack<Expression> search = new Stack<>();
        search.add(expression);

        while (!search.isEmpty()) {
            Expression e = search.pop();
            if (e instanceof Jmlish) {
                return true;
            }

            if (e instanceof BinaryExpr be) {
                if (be.getOperator() == BinaryExpr.Operator.IMPLICATION)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.RIMPLICATION)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.EQUIVALENCE)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.SUB_LOCK)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.SUB_LOCKE)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.SUBTYPE)
                    return true;
                if (be.getOperator() == BinaryExpr.Operator.RANGE)
                    return true;
            }

            for (Node childNode : e.getChildNodes()) {
                if (childNode instanceof Expression ex)
                    search.add(ex);
            }
        }
        return false;
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
