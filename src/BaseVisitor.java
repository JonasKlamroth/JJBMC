import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.apache.logging.log4j.core.config.Configurator;
import org.jmlspecs.openjml.JmlTree;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import static com.sun.tools.javac.tree.JCTree.*;
import static org.jmlspecs.openjml.JmlTree.*;

/**
 * Created by jklamroth on 11/13/18.
 */
public class BaseVisitor extends FilterVisitor {
    private static Logger log = LogManager.getLogger(BaseVisitor.class);
    private boolean used = false;
    private JCTree.JCClassDecl returnExcClass;
    private final ClassReader reader;
    private final Symtab syms;
    private final Map<String, List<JCExpression>> functionsByNames = new HashMap<>();
    private final ArrayList<String> calledFunctions = new ArrayList<>();
    private List<JCExpression> invariants = List.nil();
    public static Maker M;
    public static Context context;
    private List<JCTree> newDefs;
    public static BaseVisitor instance;


    public BaseVisitor(Context context, JmlTree.Maker maker) {
        super(context, maker);
        if(instance == null) {
            this.instance = this;
        }
        this.context = context;
        this.M = maker;
        this.syms = Symtab.instance(context);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
        TranslationUtils.init(context);
    }

    @Override
    public JCTree visitJmlTypeClauseExpr(JmlTypeClauseExpr that, Void p) {
        return super.visitJmlTypeClauseExpr(that, p);
    }

    @Override
    public JCTree visitJmlCompilationUnit(JmlCompilationUnit that, Void p) {
        if(!used) {
            used = true;
            JmlCompilationUnit cu = (JmlCompilationUnit) super.visitJmlCompilationUnit(that, p);
            cu.defs = cu.defs.prepend(M.Import(M.Ident(M.Name("org.cprover.CProver")), false));
            return cu;
        } else {
            return null;
        }
    }



    @Override
    public JCTree visitJmlClassDecl(JmlTree.JmlClassDecl that, Void p) {
        if(that.sym.flatname.toString().contains("$")) {
            ErrorLogger.warn("Inner classes currently only copied.");
            return that;
        }
        Symbol.ClassSymbol classSymbol = reader.defineClass(M.Name("ReturnException"), that.sym);
        classSymbol.sourcefile = that.sourcefile;
        classSymbol.completer = null;
        classSymbol.flatname = M.Name("ReturnException");
        returnExcClass = M.ClassDef(M.Modifiers(0L), M.Name("ReturnException"), List.nil(),
                M.Type(syms.runtimeExceptionType),
                com.sun.tools.javac.util.List.nil(),
                com.sun.tools.javac.util.List.nil());
        returnExcClass.sym = classSymbol;
        returnExcClass.type = classSymbol.type;
        //make it static
        returnExcClass.mods.flags |= 8L;
        //make it public
        returnExcClass.mods.flags |= 1L;
        for(JmlTypeClause cl : that.typeSpecs.clauses) {
            if(cl instanceof JmlTypeClauseExpr) {
                invariants = invariants.append(((JmlTypeClauseExpr) cl).expression);
            } else {
                throw new RuntimeException("Unsupported type specification: " + cl.toString());
            }
        }
        newDefs = List.nil();
        FunctionCallsVisitor fcv = new FunctionCallsVisitor(context, M);
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
                if (calledFunctions.contains(((JmlMethodDecl) def).getName().toString()) || (((JmlMethodDecl) def).getName().toString().equals("<init>") && ((that.mods.flags & 1024) == 0))) {
                    newDefs = newDefs.append(new SymbFunctionVisitor(context, M, this).copy(def));
                }
            }
        }
        for (JCTree def : that.defs) {
            if (def instanceof JmlMethodDecl) {
                newDefs = newDefs.append(new VerifyFunctionVisitor(context, M, this).copy(def));
                if(!((JmlMethodDecl) def).name.toString().equals("<init>")) {
                    newDefs = newDefs.append(def);
                }
            } else if(def instanceof JmlClassDecl) {
                BaseVisitor bv = new BaseVisitor(context, M);
                JmlClassDecl copiedClass = bv.copy((JmlClassDecl)def);
                newDefs = newDefs.append(copiedClass);
            } else {
                newDefs = newDefs.append(def);
            }
        }
        newDefs = newDefs.append(returnExcClass);
        that.defs = newDefs;

        return that;

    }

    public JCClassDecl getExceptionClass() {
        return returnExcClass;
    }

    public List<JCExpression> getAssignablesForName(String n) {
        return functionsByNames.get(n);
    }

    public boolean hasSymbolicVersion(String meth) {
        return calledFunctions.contains(meth);
    }

    public List<JCExpression> getInvariants() {
        return invariants;
    }

    public Symbol.MethodSymbol getMethodSymbol(String name) {
        for(JCTree d : newDefs) {
            if(d instanceof JCMethodDecl) {
                if(((JCMethodDecl) d).name.toString().equals(name)) {
                    return ((JCMethodDecl) d).sym;
                }
            }
        }
        throw new RuntimeException("Could not find symbol for funkction: " + name);
    }
}
