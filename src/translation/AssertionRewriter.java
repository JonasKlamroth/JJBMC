package translation;

import cli.ErrorLogger;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import exceptions.TranslationException;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jetbrains.annotations.NotNull;

import java.util.*;


/**
 * Created by jklamroth on 11/13/18.
 */
public class AssertionRewriter extends ModifierVisitor<Object> {
    private static final Logger log = LogManager.getLogger(AssertionRewriter.class);
    private final Map<String, List<Expression>> functionsByNames = new HashMap<>();
    private final ArrayList<String> calledFunctions = new ArrayList<>();
    private boolean used = false;
    private ClassOrInterfaceDeclaration returnExcClass;
    private List<Expression> invariants = new LinkedList<>();


    @Override
    public Visitable visit(CompilationUnit n, Object arg) {
        if (!used) {
            used = true;
            n.addImport("org.cprover.CProver", false, false);
            return super.visit(n, arg);
        } else {
            return null;
        }
    }

    @Override
    public Visitable visit(ClassOrInterfaceDeclaration that, Object arg) {
        if (that.isInnerClass()) {
            ErrorLogger.warn("Inner classes currently only copied.");
            return that;
        }

        super.visit(that, arg);

        if (!that.isInnerClass()) {
            that.addMember(createExceptionClass());
        }

        /*for (JmlTypeClause cl : that.typeSpecs.clauses) {
            if (cl instanceof JmlTypeClauseExpr) {
                invariants = invariants.append(((JmlTypeClauseExpr) cl).expression);
            } else {
                throw new UnsupportedException("Unsupported type specification: " + cl.toString());
            }
        }*/ //TODO weigl??
        return that;
    }



    @NotNull
    private static ClassOrInterfaceDeclaration createExceptionClass() {
        var exceptionClass = new ClassOrInterfaceDeclaration();
        exceptionClass.addModifier(Modifier.DefaultKeyword.PUBLIC, Modifier.DefaultKeyword.STATIC);
        exceptionClass.setName("ReturnException");
        exceptionClass.setExtendedTypes(new NodeList<>(new ClassOrInterfaceType("Exception")));
        return exceptionClass;
    }

    @Override
    public Visitable visit(MethodDeclaration n, Object arg) {
        //var fcv = new FunctionCallsVisitor();
        //functionsByNames.put(n.getNameAsString(), fcv.getAssignables());
        //fcv.resetAssignables();
        //calledFunctions.addAll(fcv.getCalledFunctions());

        //newDefs.add(new SymbFunctionVisitor(this).copy(def));
        //var copy = new Jml2JavaConverter(this).copy(def);
        return super.visit(n, arg);
    }

    public ClassOrInterfaceDeclaration getExceptionClass() {
        return returnExcClass;
    }

    public List<Expression> getAssignablesForName(String n) {
        return functionsByNames.get(n);
    }

    public boolean hasSymbolicVersion(String meth) {
        return calledFunctions.contains(meth);
    }

    public List<Expression> getInvariants() {
        return invariants;
    }
}
