package utils;

import Exceptions.TranslationException;
import translation.BaseVisitor;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;

public class IdentifierVisitor extends JmlTreeScanner {
    private List<JCTree.JCExpression> locSets = List.nil();
    private List<Symbol.VarSymbol> localVars = List.nil();
    private final List<JCTree.Tag> assignOps = List.of(JCTree.Tag.BITOR_ASG,
        JCTree.Tag.BITXOR_ASG,
        JCTree.Tag.BITAND_ASG,
        JCTree.Tag.SL_ASG,
        JCTree.Tag.SR_ASG,
        JCTree.Tag.USR_ASG,
        JCTree.Tag.PLUS_ASG,
        JCTree.Tag.MINUS_ASG,
        JCTree.Tag.MUL_ASG,
        JCTree.Tag.DIV_ASG,
        JCTree.Tag.MOD_ASG,
        JCTree.Tag.PREINC,
        JCTree.Tag.PREDEC,
        JCTree.Tag.POSTINC,
        JCTree.Tag.POSTDEC);

    public IdentifierVisitor() {
        super();
    }

    public static List<JCTree.JCExpression> getAssignLocations(JCTree.JCStatement st) {
        IdentifierVisitor visitor = new IdentifierVisitor();
        visitor.scan(st);
        List<JCTree.JCExpression> res = List.nil();
        for (JCTree.JCExpression e : visitor.locSets) {
            if (e instanceof JCTree.JCIdent) {
                if (visitor.localVars.contains(((JCTree.JCIdent) e).sym)) {
                    continue;
                }
            }
            res = res.append(e);
        }
        return res;
    }

    @Override
    public void visitApply(JCTree.JCMethodInvocation tree) {
        String functionName = "";
        List<String> params = List.nil();
        if (tree.meth instanceof JCTree.JCIdent) {
            JCTree.JCIdent i = ((JCTree.JCIdent) tree.meth);
            functionName = i.name.toString();
            Symbol.MethodSymbol sym = (Symbol.MethodSymbol) i.sym;
            if (sym == null) {
                sym = BaseVisitor.instance.getMethodSymbol(functionName);
            }
            if (sym == null) {
                throw new TranslationException("Could not find symbol for function: " + functionName);
            }
            for (Symbol.VarSymbol v : sym.params) {
                params = params.append(v.name.toString());
            }
        } else if (tree.meth instanceof JCTree.JCFieldAccess) {
            functionName = ((JCTree.JCFieldAccess) tree.meth).name.toString();
        }
        if (BaseVisitor.instance != null) {
            List<JCTree.JCExpression> assigns = BaseVisitor.instance.getAssignablesForName(functionName);
            if (assigns != null) {
                List<JCTree.JCExpression> processedAssigns = List.nil();
                for (int j = 0; j < assigns.size(); ++j) {
                    JCTree.JCExpression assign = assigns.get(j);
                    for (int i = 0; i < params.size(); ++i) {
                        assign = ReplaceVisitor.replace(params.get(i), tree.args.get(i), assign, BaseVisitor.M);
                    }
                    processedAssigns = processedAssigns.append(assign);
                }
                locSets = locSets.prependList(processedAssigns);
            }
        }
    }

    @Override
    public void visitJmlForLoop(JmlTree.JmlForLoop that) {
        //do nothing here
    }

    @Override
    public void visitJmlWhileLoop(JmlTree.JmlWhileLoop that) {
        //do nothing here
    }

    @Override
    public void visitUnary(JCTree.JCUnary tree) {
        if (assignOps.contains(tree.getTag())) {
            locSets = locSets.prepend(tree.arg);
        }
        super.visitUnary(tree);
    }

    @Override
    public void visitAssignop(JCTree.JCAssignOp tree) {
        locSets = locSets.prepend(tree.lhs);
        super.visitAssignop(tree);
    }

    @Override
    public void visitJmlVariableDecl(JmlTree.JmlVariableDecl that) {
        localVars = localVars.append(that.sym);
        super.visitJmlVariableDecl(that);
    }

    @Override
    public void visitAssign(JCTree.JCAssign tree) {
        locSets = locSets.prepend(tree.lhs);
        super.visitAssign(tree);
    }
}
