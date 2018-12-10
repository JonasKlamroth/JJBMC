import com.sun.source.tree.AnnotationTree;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;

import static com.sun.tools.javac.tree.JCTree.*;
import static org.jmlspecs.openjml.JmlTree.*;

/**
 * Created by jklamroth on 11/13/18.
 */
public class BaseVisitor extends JmlTreeCopier {
    private JCTree.JCClassDecl returnExcClass;
    private final ClassReader reader;
    private final Symtab syms;


    public BaseVisitor(Context context, JmlTree.Maker maker) {
        super(context, maker);
        this.syms = Symtab.instance(context);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
    }

    @Override
    public JCTree visitJmlCompilationUnit(JmlCompilationUnit that, Void p) {
        JmlCompilationUnit cu = (JmlCompilationUnit) super.visitJmlCompilationUnit(that, p);
        cu.defs = cu.defs.prepend(M.Import(M.Ident(M.Name("org.cprover.CProver")), false));
        return cu;
    }

    @Override
    public JCTree visitJmlClassDecl(JmlTree.JmlClassDecl that, Void p) {
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
        JmlClassDecl copy = (JmlClassDecl)super.visitJmlClassDecl(that, p);
        List<JCTree> newDefs = List.nil();
        for(JCTree def : copy.defs) {
            if(def instanceof JmlMethodDecl && !((JmlMethodDecl) def).getName().toString().equals("<init>")) {
                newDefs = newDefs.append(new VerifyFunctionVisitor(context, M, this).copy(def));
                newDefs = newDefs.append(new SymbFunctionVisitor(context, M, this).copy(def));
            } else {
                newDefs = newDefs.append(def);
            }
        }
        newDefs = newDefs.append(returnExcClass);
        copy.defs = newDefs;

        return copy;
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
}
