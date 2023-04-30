package translation;

import cli.ErrorLogger;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.resolution.MethodUsage;
import exceptions.TranslationException;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

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
    private List<Node> newDefs;


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
        if(that.isInnerClass()){
            ErrorLogger.warn("Inner classes currently only copied.");
            return that;
        }

        var exceptionClass = new ClassOrInterfaceDeclaration();
        exceptionClass.addModifier(Modifier.DefaultKeyword.PUBLIC, Modifier.DefaultKeyword.STATIC);
        exceptionClass.setName("ReturnException");
        exceptionClass.setExtendedTypes(new NodeList<>(new ClassOrInterfaceType("Exception")));

        /*for (JmlTypeClause cl : that.typeSpecs.clauses) {
            if (cl instanceof JmlTypeClauseExpr) {
                invariants = invariants.append(((JmlTypeClauseExpr) cl).expression);
            } else {
                throw new UnsupportedException("Unsupported type specification: " + cl.toString());
            }
        }*/ //TODO weigl??

        newDefs = new LinkedList<>();
        var fcv = new FunctionCallsVisitor();
        for (JCTree def : that.defs) {
            if (def instanceof JmlMethodDecl && !((JmlMethodDecl) def).getName().toString().equals("<init>")) {
                fcv.copy(def);
                functionsByNames.put(((JmlMethodDecl) def).getName().toString(), fcv.getAssignables());
            }
            fcv.resetAssignables();

        }
        calledFunctions.addAll(fcv.getCalledFunctions());
        for (JCTree def : that.defs) {
            if (def instanceof JmlMethodDecl) {
                if (calledFunctions.contains(((JmlMethodDecl) def).getName().toString()) ||
                    (((JmlMethodDecl) def).getName().toString().equals("<init>") && ((that.mods.flags & 1024) == 0))) {
                    newDefs = newDefs.append(new SymbFunctionVisitor(context, M, this).copy(def));
                }
            }
        }
        for (JCTree def : that.defs) {
            if (def instanceof JmlMethodDecl) {
                JCTree copy = new VerifyFunctionVisitor(context, M, this).copy(def);
                if (copy != null) {
                    newDefs = newDefs.append(copy);
                }
                if (!((JmlMethodDecl) def).name.toString().equals("<init>")) {
                    newDefs = newDefs.append(def);
                }
            } else if (def instanceof JmlClassDecl) {
                BaseVisitor bv = new BaseVisitor(context, M);
                JmlClassDecl copiedClass = bv.copy((JmlClassDecl) def);
                newDefs = newDefs.append(copiedClass);
            } else {
                newDefs = newDefs.append(def);
            }
        }
        newDefs = newDefs.append(returnExcClass);
        that.defs = newDefs;

        return that;

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

    public MethodDeclaration getMethodSymbol(String name) {
        for (JCTree d : newDefs) {
            if (d instanceof JCMethodDecl) {
                if (((JCMethodDecl) d).name.toString().equals(name)) {
                    return ((JCMethodDecl) d).sym;
                }
            }
        }
        throw new TranslationException("Could not find symbol for function: " + name);
    }
}
