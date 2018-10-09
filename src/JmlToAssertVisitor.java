import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.MethodTree;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class JmlToAssertVisitor extends JmlTreeCopier {
    private final JmlTree.Maker M;
    private final Context context;
    private final Log log;
    private final Names names;
    private final Nowarns nowarns;
    private final Symtab syms;
    private final Types types;
    private final Utils utils;
    private final JmlTypes jmltypes;
    private final JmlSpecs specs;
    private final JmlTreeUtils treeutils;
    private final JmlAttr attr;
    private final Name resultName;
    private final Name exceptionName;
    private final Name exceptionNameCall;
    private final Name terminationName;
    private final ClassReader reader;
    private final Symbol.ClassSymbol utilsClass;
    private final JCTree.JCIdent preLabel;
    private Set<JCTree.JCExpression> ensuresList = new HashSet<>();
    private Set<JCTree.JCExpression> requiresList = new HashSet<>();

    @Override
    public JCTree visitMethodInvocation(MethodInvocationTree node, Void p) {
        return super.visitMethodInvocation(node, p);
    }

    public JmlToAssertVisitor(Context context, JmlTree.Maker maker) {
        super(context, maker);
        this.context = context;
        this.log = Log.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.nowarns = Nowarns.instance(context);
        this.syms = Symtab.instance(context);
        this.types = Types.instance(context);
        this.utils = Utils.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.jmltypes = JmlTypes.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.attr = JmlAttr.instance(context);
        this.resultName = names.fromString(Strings.resultVarString);
        this.exceptionName = names.fromString(Strings.exceptionVarString);
        this.exceptionNameCall = names.fromString(Strings.exceptionCallVarString);
        this.terminationName = names.fromString(Strings.terminationVarString);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
        this.utilsClass = reader.enterClass(names.fromString(Strings.runtimeUtilsFQName));
        this.preLabel = treeutils.makeIdent(Position.NOPOS, Strings.empty, syms.intType);
    }

    @Override
    public JCTree visitJmlMethodClauseExpr(JmlTree.JmlMethodClauseExpr that, Void p) {
        JCTree.JCExpression expression = that.expression;
        if(that.token == JmlTokenKind.ENSURES) {
            ensuresList.add(expression);
        } else {
            requiresList.add(expression);
        }
        return super.visitJmlMethodClauseExpr(that, p);
    }

    @Override
    public JCTree visitJmlMethodDecl(JmlTree.JmlMethodDecl that, Void p) {
        requiresList.clear();
        ensuresList.clear();
        JmlTree.JmlMethodDecl copy = (JmlTree.JmlMethodDecl)super.visitJmlMethodDecl(that, p);
        List<JCTree.JCStatement> ensStmts = new ArrayList<>();
        ensuresList.forEach(ensures -> ensStmts.add(M.at(copy.body.pos).Assert(ensures, null)));
        List<JCTree.JCStatement> reqStmts = new ArrayList<>();
        requiresList.forEach(requires -> {
            JCTree.JCIdent classIvil = M.Ident(M.Name("CProver"));
            JCTree.JCFieldAccess selectIvilSet = M.Select(classIvil, M.Name("assume"));
            JCTree.JCExpression args[] = new JCTree.JCExpression[]{requires};
            com.sun.tools.javac.util.List<JCTree.JCExpression> largs = com.sun.tools.javac.util.List.from(args);
            reqStmts.add(M.at(that.body.pos).Exec(
                    M.Apply(com.sun.tools.javac.util.List.nil(), selectIvilSet, largs)));
        });
        copy.body = M.Block(0L, copy.body.getStatements().appendList(com.sun.tools.javac.util.List.from(ensStmts)).prependList(com.sun.tools.javac.util.List.from(reqStmts)));
        return copy;
    }

    @Override
    public JCTree visitJmlCompilationUnit(JmlTree.JmlCompilationUnit that, Void p) {
        JmlTree.JmlCompilationUnit cu = (JmlTree.JmlCompilationUnit) super.visitJmlCompilationUnit(that, p);
        cu.defs = cu.defs.prepend(M.Import(M.Ident(M.Name("org.cprover.CProver")), false));
        return cu;
    }
}