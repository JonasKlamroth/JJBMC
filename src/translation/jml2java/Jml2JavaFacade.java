package translation.jml2java;

import cli.CLI;
import cli.MyPPrintVisitor;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.expr.JmlMultiCompareExpr;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NonNull;

import java.util.List;
import java.util.NoSuchElementException;
import java.util.Stack;
import java.util.concurrent.atomic.AtomicBoolean;

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
        return new AssertStmt(e);
    }

    public static Statement assume(Expression ensures) {
        var r = translate(ensures, TranslationMode.ASSUME);
        r.necessaryVars.addAll(r.statements);
        r.necessaryVars.add(assumeStatement(r.value));

        return new BlockStmt(r.necessaryVars);
    }

    public static BlockStmt assert_(Expression requires) {
        var r = translate(requires, TranslationMode.ASSERT);
        r.necessaryVars.addAll(r.statements);
        r.necessaryVars.add(assertStatement(r.value));

        return new BlockStmt(r.necessaryVars);
    }

    public static NodeList<JmlQuantifiedExpr> getRelevantQuantifiers(Expression expr) {
        Node node = expr;
        NodeList<JmlQuantifiedExpr> res = new NodeList<>();
        node = node.getParentNode().get();
        while (node != null) {
            if(!(node instanceof Expression)) {
                break;
            } else if(node instanceof JmlQuantifiedExpr) {
                res.add((JmlQuantifiedExpr) node);
            }
            node = node.getParentNode().isPresent() ? node.getParentNode().get() : null;
        }
        res.removeIf(v -> !isSubNode(expr, QuantifierSplitter.getVariable(v).getName()));
        return res;
    }

    // Returns a list of statements that save expressions under "\old"
    public static List<Statement> storeOlds(Expression requires) {
        class OldVisitor extends ModifierVisitor<Object> {
            NodeList<JmlQuantifiedExpr> currentQuantifiers = new NodeList<>();
            NodeList<Statement> statements = new NodeList<>();

            public static NodeList<Statement> run(Expression expr) {
                OldVisitor v = new OldVisitor();
                expr.accept(v, null);
                return v.statements;
            }

            @Override
            public Visitable visit(JmlQuantifiedExpr jmlQuantifiedExpr, Object arg) {
                currentQuantifiers.add(jmlQuantifiedExpr);
                Visitable res = super.visit(jmlQuantifiedExpr, arg);
                currentQuantifiers.remove(jmlQuantifiedExpr);
                return res;
            }

            @Override
            public Visitable visit(MethodCallExpr n, Object arg) {
                if (n.getNameAsString().equals("\\old")) {
                    statements.addAll(storeOld(n.getArgument(0), currentQuantifiers));
                }
                return super.visit(n, arg);
            }
        }

        return OldVisitor.run(requires);
    }

    public static boolean isSubNode(Node parent, Node child) {
        AtomicBoolean res = new AtomicBoolean(false);
        parent.walk(i -> {
                    if (i.equals(child)) {
                        res.set(true);
                    }
                }
        );
        return res.get();
    }

    public static NodeList<Statement> storeOld(Expression expression, List<JmlQuantifiedExpr> relevantQuantifiers) {
        relevantQuantifiers = new NodeList<>(relevantQuantifiers);
        relevantQuantifiers.removeIf(v -> !isSubNode(expression, QuantifierSplitter.getVariable(v).getName()));
        var translatedExpression = Jml2JavaFacade.translate(expression.clone(), TranslationMode.JAVA);
        expression.setParentNode(expression.getParentNode().get());
        var exprCopy = translatedExpression.value;
        var res = new NodeList<Statement>();
        res.addAll(translatedExpression.necessaryVars);
        res.addAll(translatedExpression.statements);

        if(relevantQuantifiers.isEmpty()) {
            // save references to old variables
            var decl = new VariableDeclarator(new VarType(), "old_" + Math.abs(expression.hashCode()), exprCopy);
            res.add(new ExpressionStmt(new VariableDeclarationExpr(decl, Modifier.finalModifier())));
            return res;
        }

        BlockStmt st = new BlockStmt();
        st.getStatements().addAll(res);
        res.clear();

        Type type = new VarType();

        ResolvedType resolvedType = null;
        Type realType = null;
        try {
            resolvedType = expression.calculateResolvedType();
            realType = resolvedType2Type(resolvedType);
        } catch (IllegalStateException e) {
            e.printStackTrace();
            System.out.println(expression);
        } catch (UnsolvedSymbolException e) {
            e.printStackTrace();
        }


        for(int i = 0; i < relevantQuantifiers.size(); ++i) {
            type = new ArrayType(realType);
        }
        VariableDeclarator varDecl = new VariableDeclarator(type,
                "old_" + Math.abs(expression.hashCode()),
                new ArrayCreationExpr(realType,
                        new NodeList<>(new ArrayCreationLevel(new IntegerLiteralExpr(String.valueOf(CLI.maxArraySize)))),
                        null));
        res.add(new ExpressionStmt(new VariableDeclarationExpr(varDecl, Modifier.finalModifier())));
        Expression e = varDecl.getNameAsExpression();
        for(int i = relevantQuantifiers.size() - 1; i >= 0; --i) {
            e = new ArrayAccessExpr(e,
                    new BinaryExpr(
                            QuantifierSplitter.getVariable(relevantQuantifiers.get(i)).getNameAsExpression(),
                            new IntegerLiteralExpr(String.valueOf(CLI.maxArraySize)),
                            BinaryExpr.Operator.REMAINDER)
                    );
        }

        e = new AssignExpr(e, exprCopy, AssignExpr.Operator.ASSIGN);
        st.addStatement(new ExpressionStmt(e));

        for(JmlQuantifiedExpr quantifiedExpr : relevantQuantifiers) {
            Expression lowerBound = QuantifierSplitter.getLowerBound(quantifiedExpr);
            var translatedLowerBound = Jml2JavaFacade.translate((Expression) lowerBound.clone().setParentNode(quantifiedExpr), TranslationMode.DEMONIC);
            lowerBound = translatedLowerBound.value;
            Expression upperBound = QuantifierSplitter.getUpperBound(quantifiedExpr);
            var translatedUpperBound = Jml2JavaFacade.translate((Expression) upperBound.clone().setParentNode(quantifiedExpr), TranslationMode.DEMONIC);
            upperBound = translatedUpperBound.value;

            var loopVarDecl = new VariableDeclarationExpr(PrimitiveType.intType(), "__tmp__" + Jml2JavaExpressionTranslator.counter.getAndIncrement());
            var loopVar = loopVarDecl.getVariable(0).getNameAsExpression();
            st.accept(new ReplaceVariable(QuantifierSplitter.getVariable(quantifiedExpr), loopVar.getNameAsString()), null);
            var forLoop = new ForStmt(new NodeList<>(new AssignExpr(loopVarDecl, lowerBound, AssignExpr.Operator.ASSIGN)),
                    new BinaryExpr(loopVar, upperBound, BinaryExpr.Operator.LESS_EQUALS),
                    new NodeList<Expression>(new UnaryExpr(loopVar, UnaryExpr.Operator.POSTFIX_INCREMENT)),
                    st);
            st = new BlockStmt();
            BlockStmt finalSt = st;
            st.addStatement(forLoop);
            translatedLowerBound.necessaryVars.forEach(s -> finalSt.addStatement(s));
            translatedLowerBound.statements.forEach(s -> finalSt.addStatement(s));
            translatedUpperBound.necessaryVars.forEach(s -> finalSt.addStatement(s));
            translatedUpperBound.statements.forEach(s -> finalSt.addStatement(s));
            st = finalSt;
        }
        res.add(st);
        return res;
    }

    public static Statement havoc(Expression expression) {
        return havoc(expression, true);
    }

    public static Statement havoc(Expression expression, boolean allowNull) {
        if(expression.toString().equals("\\nothing")) {
            return new BlockStmt();
        }
        ResolvedType type = expression.calculateResolvedType();
        var functionName = "";
        if (expression instanceof ArrayAccessExpr arrayAccessExpr) {
            if (expression.toString().contains("*") || expression.toString().contains("..")) {
                return havocArray(arrayAccessExpr);
            }
        }
        if (type.equals(ResolvedPrimitiveType.INT)) {
            functionName = "nondetInt";
        } else if (type.equals(ResolvedPrimitiveType.CHAR)) {
            functionName = "nondetChar";
        } else if (type.equals(ResolvedPrimitiveType.BOOLEAN)) {
            functionName = "nondetBoolean";
        } else if (type.equals(ResolvedPrimitiveType.SHORT)) {
            functionName = "nondetShort";
        } else if (type.equals(ResolvedPrimitiveType.BYTE)) {
            functionName = "nondetByte";
        } else if (type.equals(ResolvedPrimitiveType.LONG)) {
            functionName = "nondetLong";
        } else if (type.equals(ResolvedPrimitiveType.FLOAT)) {
            functionName = "nondetFloat";
        } else if (type.equals(ResolvedPrimitiveType.DOUBLE)) {
            functionName = "nondetDouble";
        } else {
            if (allowNull) {
                functionName = "nondetWithNull";
            } else {
                functionName = "nondetWithoutNull";
            }
        }
        MethodCallExpr nondetFunction = new MethodCallExpr(new NameExpr("CProver"), functionName, new NodeList<>());
        if(expression instanceof VariableDeclarationExpr variableDeclarationExpr) {
            expression = variableDeclarationExpr.getVariable(0).getNameAsExpression();
        }
        return new ExpressionStmt(new AssignExpr(expression, nondetFunction, AssignExpr.Operator.ASSIGN));
    }

    public static Statement havocArray(ArrayAccessExpr expr) {
        BlockStmt blockStmt = new BlockStmt();
        blockStmt.setParentNode(expr.getParentNode().get());
        var min = new IntegerLiteralExpr("0");
        var max = new FieldAccessExpr(expr.getName(), "length");
        var loopVarDecl = new VariableDeclarationExpr(PrimitiveType.intType(), "__tmp__" + Jml2JavaExpressionTranslator.counter.getAndIncrement());
        var loopVar = loopVarDecl.getVariable(0).getNameAsExpression();
        var element = expr.clone();
        element.setParentNode(blockStmt);
        element.setIndex(loopVar);
        var forLoop = new ForStmt(new NodeList<>(new AssignExpr(loopVarDecl, min, AssignExpr.Operator.ASSIGN)),
                new BinaryExpr(loopVar, max, BinaryExpr.Operator.LESS),
                new NodeList<Expression>(new UnaryExpr(loopVar, UnaryExpr.Operator.POSTFIX_INCREMENT)),
                new BlockStmt());
        blockStmt.addStatement(forLoop);
        var havocElement = havoc(element);
        ((BlockStmt)(forLoop.getBody())).addStatement(havocElement);

        return blockStmt;
    }

    public static CompilationUnit translate(CompilationUnit cu) {
        //Normlize all binary expressions
        cu.accept(new NormlizeBinaryExpressions(), null);

        //add method stubs for call to contracts
        cu.accept(new CreateMethodContracts(), null);

        //rewrite methods and loops
        var res = (CompilationUnit) cu.accept(new EmbeddContracts(), null);


        // add exception type to the compilation unit
        cu.addType(Jml2JavaFacade.createExceptionClass());

        // add CProver import statement
        cu.addImport(Jml2JavaFacade.createCProverImport());
        return res;
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
        @NonNull
        NodeList<Statement> necessaryVars = new NodeList<>();

        public Result(@NonNull Expression e) {
            this.value = e;
        }

        public Result(NodeList<Statement> statements, @NonNull Expression e) {
            this.value = e;
            this.statements = statements;
        }

        public Result(NodeList<Statement> statements, NameExpr e, Statement varDef) {
            this.statements = statements;
            this.value = e;
            this.necessaryVars.add(varDef);
        }

        public Result(NodeList<Statement> statements, NameExpr e, NodeList<Statement> varDefs) {
            this.statements = statements;
            this.value = e;
            this.necessaryVars = varDefs;
        }
    }

    /**
     * Fixes an error in JavaParser pretty printing of JML-contracts
     *
     * @param translation
     * @return
     */
    public static String pprint(Node translation) {
        DefaultPrettyPrinter pp = new DefaultPrettyPrinter(
                MyPPrintVisitor::new, new DefaultPrinterConfiguration());
        return pp.print(translation);
    }

    public static ImportDeclaration createCProverImport() {
        return new ImportDeclaration("org.cprover.CProver", false, false);
    }

    public static ClassOrInterfaceDeclaration createExceptionClass() {
        var exceptionClass = new ClassOrInterfaceDeclaration();
        //exceptionClass.addModifier(Modifier.DefaultKeyword.PUBLIC, Modifier.DefaultKeyword.STATIC);
        exceptionClass.setName("ReturnException");
        exceptionClass.setExtendedTypes(new NodeList<>(new ClassOrInterfaceType().setName("Exception")));
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

            if (e instanceof NameExpr ne) {
                if(ne.getNameAsString().startsWith("\\")) {
                    return true;
                }
            }

            if (e instanceof MethodCallExpr methodCallExpr) {
                if(methodCallExpr.getNameAsString().startsWith("\\")) {
                    return true;
                }
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
                if (be.getOperator() == BinaryExpr.Operator.ANTIVALENCE)
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
            return new ClassOrInterfaceType().setName(rType.getQualifiedName());
        }

        throw new RuntimeException("Unsupported type");
    }
}
