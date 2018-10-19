import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.ExpressionStatementTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.VariableTree;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.JmlTreeVisitor;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
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
    private JmlTree.JmlMethodDecl currentMethod;
    private int boolVarCounter = 0;
    private LinkedList<JCTree.JCStatement> newStatements = new LinkedList<>();
    private LinkedList<JCTree.JCStatement> combinedNewStatements = new LinkedList<>();
    private Symbol returnBool = null;
    private List<Object> visited = new ArrayList<>();
    private boolean translationMode = false;

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
        returnBool = null;
        translationMode = true;
        JCTree copy = super.visitJmlMethodClauseExpr(that, p);
        translationMode = false;
        if(that.token == JmlTokenKind.ENSURES) {
            if(returnBool != null) {
                newStatements.add(M.at(currentMethod.body.pos).Assert(M.Ident(returnBool), null));
            }
        } else {
            if(returnBool != null) {
                JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
                JCTree.JCFieldAccess assumeFunc = M.Select(classCProver, M.Name("assume"));
                JCTree.JCExpression args[] = new JCTree.JCExpression[]{M.Ident(returnBool)};
                com.sun.tools.javac.util.List<JCTree.JCExpression> largs = com.sun.tools.javac.util.List.from(args);
                newStatements.add(M.Exec(
                        M.Apply(com.sun.tools.javac.util.List.nil(), assumeFunc, largs)));
            }
        }
        combinedNewStatements.addAll(newStatements);
        newStatements.clear();
        return copy;
    }

    @Override
    public JCTree visitJmlMethodDecl(JmlTree.JmlMethodDecl that, Void p) {
        requiresList.clear();
        ensuresList.clear();
        currentMethod = that;
        super.visitJmlMethodDecl(that, p);
//        currentMethod.body = M.Block(0L, currentMethod.body.getStatements().appendList(com.sun.tools.javac.util.List.from(ensStmts)).prependList(com.sun.tools.javac.util.List.from(reqStmts)));
        currentMethod.body = M.Block(0L, currentMethod.body.getStatements().appendList(com.sun.tools.javac.util.List.from(combinedNewStatements)));
        combinedNewStatements.clear();
        return currentMethod;
    }

    @Override
    public JCTree visitJmlCompilationUnit(JmlTree.JmlCompilationUnit that, Void p) {
        JmlTree.JmlCompilationUnit cu = (JmlTree.JmlCompilationUnit) super.visitJmlCompilationUnit(that, p);
        cu.defs = cu.defs.prepend(M.Import(M.Ident(M.Name("org.cprover.CProver")), false));
        return cu;
    }

    @Override
    public JCTree visitJmlQuantifiedExpr(JmlTree.JmlQuantifiedExpr that, Void p) {
        if(!visited.contains(that)) {
            JmlTree.JmlQuantifiedExpr copy = that;
            visited.add(that);
            super.copy(copy.value);
            if(copy.op == JmlTokenKind.BSFORALL) {
                JCTree.JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentMethod.sym, treeutils.makeLit(Position.NOPOS, syms.booleanType, true));
                JCTree.JCBinary b = M.Binary(JCTree.Tag.AND, M.Ident(boolVar), M.Ident(returnBool));
                newStatements.addLast(M.Exec(M.Assign(M.Ident(boolVar), b)));
                LinkedList<JCTree.JCStatement> l = new LinkedList<>();
                l.add(boolVar);
                l.add(makeStandardLoop(copy.range, newStatements));
                newStatements = l;
                returnBool = boolVar.sym;
                return M.Ident(boolVar);
            } else if(copy.op == JmlTokenKind.BSEXISTS) {
                JCTree.JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentMethod.sym, treeutils.makeLit(Position.NOPOS, syms.booleanType, false));
                JCTree.JCBinary b = M.Binary(JCTree.Tag.OR, M.Ident(boolVar), M.Ident(returnBool));
                newStatements.addLast(M.Exec(M.Assign(M.Ident(boolVar), b)));
                LinkedList<JCTree.JCStatement> l = new LinkedList<>();
                l.add(boolVar);
                l.add(makeStandardLoop(copy.range, newStatements));
                newStatements = l;
                returnBool = boolVar.sym;
                return M.Ident(boolVar);
            }
            return copy;
        }
        return that;
    }

    @Override
    public JCTree visitBinary(BinaryTree node, Void p) {
        if(!visited.contains(node) && translationMode) {
            visited.add(node);
            JCTree.JCBinary copy = (JCTree.JCBinary) super.visitBinary(node, p);
            if(copy.operator.asType().getReturnType() == syms.booleanType) {
                JCTree.JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentMethod.sym, copy);
                newStatements.addLast(boolVar);
                returnBool = boolVar.sym;
                return M.Ident(boolVar);
            }
        }
        return super.visitBinary(node, p);
    }

    @Override
    public JCTree visitLiteral(LiteralTree node, Void p) {
        if(!visited.contains(node) && translationMode) {
            visited.add(node);
            JCTree.JCLiteral copy = (JCTree.JCLiteral) super.visitLiteral(node, p);
            if(copy.type.baseType() == syms.booleanType) {
                JCTree.JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentMethod.sym, copy);
                newStatements.addLast(boolVar);
                returnBool = boolVar.sym;
                return M.Ident(boolVar);
            }
        }
        return super.visitLiteral(node, p);
    }

    private JCTree.JCExpression makeRangeCondition(int min, int max, Symbol loopVar) {
        JCTree.JCBinary lower = M.Binary(JCTree.Tag.LT, M.Literal(min), M.Ident(loopVar));
        JCTree.JCBinary upper = M.Binary(JCTree.Tag.GT, M.Literal(max), M.Ident(loopVar));
        return M.Binary(JCTree.Tag.AND, lower, upper);
    }

    private JCTree.JCStatement makeStandardLoop(JCTree.JCExpression range, List<JCTree.JCStatement> body) {
        JCTree.JCVariableDecl loopVar = treeutils.makeVarDef(syms.intType, names.fromString("i"), currentMethod.sym, treeutils.makeLit(Position.NOPOS, syms.intType, 0));
        JCTree.JCExpression loopCond = range;
        JCTree.JCExpressionStatement loopStep = M.Exec(treeutils.makeUnary(Position.NOPOS, JCTree.Tag.PREINC, treeutils.makeIdent(Position.NOPOS, loopVar.sym)));
        com.sun.tools.javac.util.List<JCTree.JCExpressionStatement> loopStepl = com.sun.tools.javac.util.List.from(Collections.singletonList(loopStep));
        JCTree.JCBlock loopBodyBlock = M.Block(0L, com.sun.tools.javac.util.List.from(body));
        com.sun.tools.javac.util.List<JCTree.JCStatement> loopVarl = com.sun.tools.javac.util.List.from(Collections.singletonList(loopVar));
        return M.ForLoop(loopVarl, loopCond, loopStepl, loopBodyBlock);
    }
}

class RangeExtractor extends JmlTreeScanner {
    private int minResult;
    private int maxResult;

    @Override
    public void visitBinary(JCTree.JCBinary tree) {
        if(tree.getKind() == Tree.Kind.GREATER_THAN) {
            if(tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER) {
                minResult = Integer.parseInt(tree.getRightOperand().getTree().toString()) + 1;
            }
            if(tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER) {
                maxResult = Integer.parseInt(tree.getLeftOperand().getTree().toString()) - 1;
            }
        }
        if(tree.getKind() == Tree.Kind.LESS_THAN) {
            if(tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER) {
                maxResult = Integer.parseInt(tree.getRightOperand().getTree().toString()) - 1;
            }
            if(tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER) {
                minResult = Integer.parseInt(tree.getLeftOperand().getTree().toString()) + 1;
            }
        }
        if(tree.getKind() == Tree.Kind.GREATER_THAN_EQUAL) {
            if(tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER) {
                minResult = Integer.parseInt(tree.getRightOperand().getTree().toString());
            }
            if(tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER) {
                maxResult = Integer.parseInt(tree.getLeftOperand().getTree().toString());
            }
        }
        if(tree.getKind() == Tree.Kind.LESS_THAN_EQUAL) {
            if(tree.getLeftOperand().getKind() == Tree.Kind.IDENTIFIER) {
                maxResult = Integer.parseInt(tree.getRightOperand().getTree().toString());
            }
            if(tree.getRightOperand().getKind() == Tree.Kind.IDENTIFIER) {
                minResult = Integer.parseInt(tree.getLeftOperand().getTree().toString());
            }
        }
        super.visitBinary(tree);
    }

    public int getMin() {
        return minResult;
    }

    public int getMax() {
        return maxResult;
    }
}