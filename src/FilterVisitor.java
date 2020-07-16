import com.sun.source.tree.AnnotatedTypeTree;
import com.sun.source.tree.AnnotationTree;
import com.sun.source.tree.ArrayAccessTree;
import com.sun.source.tree.ArrayTypeTree;
import com.sun.source.tree.AssertTree;
import com.sun.source.tree.AssignmentTree;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.BlockTree;
import com.sun.source.tree.BreakTree;
import com.sun.source.tree.CaseTree;
import com.sun.source.tree.CatchTree;
import com.sun.source.tree.ClassTree;
import com.sun.source.tree.CompilationUnitTree;
import com.sun.source.tree.CompoundAssignmentTree;
import com.sun.source.tree.ConditionalExpressionTree;
import com.sun.source.tree.ContinueTree;
import com.sun.source.tree.DoWhileLoopTree;
import com.sun.source.tree.EmptyStatementTree;
import com.sun.source.tree.EnhancedForLoopTree;
import com.sun.source.tree.ErroneousTree;
import com.sun.source.tree.ExpressionStatementTree;
import com.sun.source.tree.ForLoopTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.IfTree;
import com.sun.source.tree.ImportTree;
import com.sun.source.tree.InstanceOfTree;
import com.sun.source.tree.IntersectionTypeTree;
import com.sun.source.tree.LabeledStatementTree;
import com.sun.source.tree.LambdaExpressionTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.MemberReferenceTree;
import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.ModifiersTree;
import com.sun.source.tree.NewArrayTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.ParameterizedTypeTree;
import com.sun.source.tree.ParenthesizedTree;
import com.sun.source.tree.PrimitiveTypeTree;
import com.sun.source.tree.ReturnTree;
import com.sun.source.tree.SwitchTree;
import com.sun.source.tree.SynchronizedTree;
import com.sun.source.tree.ThrowTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.TryTree;
import com.sun.source.tree.TypeCastTree;
import com.sun.source.tree.TypeParameterTree;
import com.sun.source.tree.UnaryTree;
import com.sun.source.tree.UnionTypeTree;
import com.sun.source.tree.VariableTree;
import com.sun.source.tree.WhileLoopTree;
import com.sun.source.tree.WildcardTree;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;

/**
 * Created by jklamroth on 2/5/19.
 *
 * This Visitor is used to implement the whitelisting apprach:
 * the default is that no TreeElement is supported with some exceptions like for example
 * basic types. Everything else has to overwritten in order to prevent the exception from being thrown.
 */
public class FilterVisitor extends JmlTreeCopier {
    public FilterVisitor(Context context, JmlTree.Maker maker) {
        super(context, maker);
    }

    @Override
    public JCTree visitJmlChoose(JmlTree.JmlChoose that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlMethodDecl(JmlTree.JmlMethodDecl that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlBinary(JmlTree.JmlBinary that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlBlock(JmlTree.JmlBlock that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlConstraintMethodSig(JmlTree.JmlMethodSig that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlDoWhileLoop(JmlTree.JmlDoWhileLoop that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlEnhancedForLoop(JmlTree.JmlEnhancedForLoop that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlForLoop(JmlTree.JmlForLoop that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlGroupName(JmlTree.JmlGroupName that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlInlinedLoop(JmlTree.JmlInlinedLoop that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlMethodClauseCallable(JmlTree.JmlMethodClauseCallable that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlMethodClauseConditional(JmlTree.JmlMethodClauseConditional that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlMethodClauseDecl(JmlTree.JmlMethodClauseDecl that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlMethodClauseExpr(JmlTree.JmlMethodClauseExpr that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlMethodClauseGroup(JmlTree.JmlMethodClauseGroup that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlMethodClauseSignals(JmlTree.JmlMethodClauseSignals that, Void p) {
        if(this instanceof VerifyFunctionVisitor && ((VerifyFunctionVisitor) this).currentMethod.name.toString().equals("<init>")) {
            return super.visitJmlMethodClauseSignals(that, p);
        }
        throw new RuntimeException("Not supported: " + that.toString());
        //return super.visitJmlMethodClauseSignals(that, p);
    }

    @Override
    public JCTree visitJmlMethodClauseSigOnly(JmlTree.JmlMethodClauseSignalsOnly that, Void p) {
        if(!that.defaultClause) {
            throw new RuntimeException("Not supported: " + that.toString());
        } else {
            return super.visitJmlMethodClauseSigOnly(that, p);
        }
    }

    @Override
    public JCTree visitJmlModelProgramStatement(JmlTree.JmlModelProgramStatement that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlQuantifiedExpr(JmlTree.JmlQuantifiedExpr that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlSetComprehension(JmlTree.JmlSetComprehension that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlSingleton(JmlTree.JmlSingleton that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlStatement(JmlTree.JmlStatement that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlStatementShow(JmlTree.JmlStatementShow that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlStatementDecls(JmlTree.JmlStatementDecls that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlStatementExpr(JmlTree.JmlStatementExpr that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlStatementHavoc(JmlTree.JmlStatementHavoc that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlStatementLoopExpr(JmlTree.JmlStatementLoopExpr that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlStatementLoopModifies(JmlTree.JmlStatementLoopModifies that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlStatementSpec(JmlTree.JmlStatementSpec that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlTypeClauseConditional(JmlTree.JmlTypeClauseConditional that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlTypeClauseConstraint(JmlTree.JmlTypeClauseConstraint that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlTypeClauseDecl(JmlTree.JmlTypeClauseDecl that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlTypeClauseExpr(JmlTree.JmlTypeClauseExpr that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlTypeClauseIn(JmlTree.JmlTypeClauseIn that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlTypeClauseInitializer(JmlTree.JmlTypeClauseInitializer that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlTypeClauseMaps(JmlTree.JmlTypeClauseMaps that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlTypeClauseMonitorsFor(JmlTree.JmlTypeClauseMonitorsFor that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlTypeClauseRepresents(JmlTree.JmlTypeClauseRepresents that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitJmlWhileLoop(JmlTree.JmlWhileLoop that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    //This should be commented our only for testing
//    @Override
//    public JCTree visitAssignment(AssignmentTree node, Void p) {
//        throw new RuntimeException("Not supported: " + node.toString());
//    }

    @Override
    public JCTree visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitBreak(BreakTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitCase(CaseTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitCatch(CatchTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitClass(ClassTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitConditionalExpression(ConditionalExpressionTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitContinue(ContinueTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitErroneous(ErroneousTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitExpressionStatement(ExpressionStatementTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitEnhancedForLoop(EnhancedForLoopTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitReturn(ReturnTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitSwitch(SwitchTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitSynchronized(SynchronizedTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitThrow(ThrowTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitTry(TryTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitParameterizedType(ParameterizedTypeTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitTypeParameter(TypeParameterTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitUnary(UnaryTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitWildcard(WildcardTree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitOther(Tree node, Void p) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitLetExpr(JCTree.LetExpr that, Void p) {
        throw new RuntimeException("Not supported: " + that.toString());
    }

    @Override
    public JCTree visitAnnotatedType(AnnotatedTypeTree node, Void aVoid) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitLambdaExpression(LambdaExpressionTree node, Void aVoid) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitMemberReference(MemberReferenceTree node, Void aVoid) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitUnionType(UnionTypeTree node, Void aVoid) {
        throw new RuntimeException("Not supported: " + node.toString());
    }

    @Override
    public JCTree visitIntersectionType(IntersectionTypeTree node, Void aVoid) {
        throw new RuntimeException("Not supported: " + node.toString());
    }
}
