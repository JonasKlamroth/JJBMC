package cli;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree;
import exceptions.TranslationException;
import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTree;
import utils.TranslationUtils;

public class CostumPrettyPrinter extends JmlPretty {

    public static Map<JCTree, JCTree> assertMap = new HashMap<>();
    int currentLine = 1;
    private Set<String> assertVars = new HashSet<>();

    public CostumPrettyPrinter(Writer out, boolean sourceOutput) {
        super(out, sourceOutput);
        TraceInformation.reset();
    }

    public static PrettyPrintInformation prettyPrint(JCTree tree) {
        try {
            StringWriter sw = new StringWriter();
            CostumPrettyPrinter cpp = new CostumPrettyPrinter(sw, true);
            tree.accept(cpp);
            //for(int key : cpp.lineMap.keySet()) {
            //    System.out.println(key + " : " + cpp.lineMap.get(key));
            //}
            TraceInformation.setExpressionMap(CLI.expressionMap);
            return new PrettyPrintInformation(sw.toString());
        } catch (Exception var3) {
            throw new TranslationException("Error pretty printing translated AST.");
        }
    }

    @Override
    public void println() throws IOException {
        currentLine += 1;
        super.println();
    }

    @Override
    public void visitAnnotation(JCTree.JCAnnotation tree) {
        //super.visitAnnotation(tree);
    }

    @Override
    public void visitApply(JCTree.JCMethodInvocation tree) {
        super.visitApply(tree);
    }

    @Override
    public void visitJmlMethodDecl(JmlTree.JmlMethodDecl that) {
        TraceInformation.addMethod(currentLine + 1, that.getName().toString());
        TraceInformation.addLineEquality(currentLine + 1, TranslationUtils.getLineNumber(that));
        super.visitJmlMethodDecl(that);
    }

    @Override
    public void visitIdent(JCTree.JCIdent tree) {
        super.visitIdent(tree);
        if (!(tree.sym instanceof Symbol.MethodSymbol) && !tree.toString().equals("this")) {
            assertVars.add(tree.toString());
        }
    }

    @Override
    public void visitAssert(JCTree.JCAssert tree) {
        assertVars = new HashSet<>();
        super.visitAssert(tree);
        TraceInformation.addAssertVars(currentLine, assertVars);
        if (tree.detail == null && assertMap.containsKey(tree) && assertMap.get(tree) != null) {
            TraceInformation.addAssert(currentLine, assertMap.get(tree).toString());
        } else {
            if (tree.detail != null) {
                TraceInformation.addAssert(currentLine, tree.detail.toString());
            } else {
                TraceInformation.addAssert(currentLine, tree.toString());
            }
        }
        assertVars = new HashSet<>();
    }

    @Override
    public void visitSelect(JCTree.JCFieldAccess tree) {
        super.visitSelect(tree);
        assertVars.add(tree.toString());
    }

    @Override
    public void visitVarDef(JCTree.JCVariableDecl that) {
        super.visitVarDef(that);
        if (that.sym.owner instanceof Symbol.MethodSymbol && !that.sym.owner.name.toString().equals("<init>")) {
            return;
        }
        TraceInformation.addLineEquality(currentLine, TranslationUtils.getLineNumber(that));
    }

    @Override
    public void visitClassDef(JCTree.JCClassDecl tree) {
        TraceInformation.addLineEquality(currentLine + 1, TranslationUtils.getLineNumber(tree));
        super.visitClassDef(tree);
    }

    @Override
    public void visitBlock(JCTree.JCBlock tree) {
        try {
            this.print("{");
            this.println();
            this.indent();
            for (JCTree.JCStatement st : tree.getStatements()) {
                this.align();
                this.printStat(st);
                if (!(st instanceof JCTree.JCBlock)) {
                    TraceInformation.addLineEquality(currentLine, TranslationUtils.getLineNumber(st));
                }
                this.println();
            }
            this.undent();
            this.align();
            this.print("}");
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
