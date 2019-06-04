import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import static com.sun.tools.javac.tree.JCTree.*;
import static org.jmlspecs.openjml.JmlTree.*;

/**
 * Created by jklamroth on 11/13/18.
 */
public class BaseVisitor extends FilterVisitor {
    private boolean used = false;
    private JCTree.JCClassDecl returnExcClass;
    private final ClassReader reader;
    private final Symtab syms;
    private final Map<String, List<JCExpression>> functionsByNames = new HashMap<>();
    private final ArrayList<String> calledFunctions = new ArrayList<>();


    public BaseVisitor(Context context, JmlTree.Maker maker) {
        super(context, maker);
        this.syms = Symtab.instance(context);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
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
        if(!that.sym.flatname.toString().contains("$")) {
            Symbol.ClassSymbol classSymbol = reader.defineClass(M.Name("ReturnException"), that.sym);
            classSymbol.sourcefile = that.sourcefile;
            classSymbol.completer = null;
            classSymbol.flatname = M.Name("ReturnException");
            returnExcClass = M.ClassDef(M.Modifiers(8L), M.Name("ReturnException"), List.nil(),
                    M.Type(syms.runtimeExceptionType),
                    com.sun.tools.javac.util.List.nil(),
                    com.sun.tools.javac.util.List.nil());
            returnExcClass.sym = classSymbol;
            returnExcClass.type = classSymbol.type;
            JmlClassDecl copy = that;
            List<JCTree> newDefs = List.nil();
            FunctionCallsVisitor fcv = new FunctionCallsVisitor(context, M);
            for (JCTree def : copy.defs) {
                if (def instanceof JmlMethodDecl && !((JmlMethodDecl) def).getName().toString().equals("<init>")) {
                    fcv.copy(def);
                    functionsByNames.put(((JmlMethodDecl) def).getName().toString(), fcv.assignables);
                }
                fcv.assignables = List.nil();
            }
            calledFunctions.addAll(fcv.calledFunctions);
            for (JCTree def : copy.defs) {
                if (def instanceof JmlMethodDecl) {
                    newDefs = newDefs.append(new VerifyFunctionVisitor(context, M, this).copy(def));
                    if (calledFunctions.contains(((JmlMethodDecl) def).getName().toString()) || (((JmlMethodDecl) def).getName().toString().equals("<init>") && ((that.mods.flags & 1024) == 0))) {
                        newDefs = newDefs.append(new SymbFunctionVisitor(context, M, this).copy(def));
                    }
                } else {
                    newDefs = newDefs.append(def);
                }
            }
            newDefs = newDefs.append(returnExcClass);
            copy.defs = newDefs;

            return copy;
        } else {
            System.out.println("NOTE: Inner classes do not get translated but only copied.");
        }
        return that;
    }

    @Override
    public JCTree visitJmlMethodDecl(JmlMethodDecl that, Void p) {
        JmlMethodDecl copy = (JmlMethodDecl)super.visitJmlMethodDecl(that, p);
        copy.sym = that.sym;
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
}
