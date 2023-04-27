package translation;

import static com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import static com.sun.tools.javac.tree.JCTree.JCAssert;
import static com.sun.tools.javac.tree.JCTree.JCExpression;
import static com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import static com.sun.tools.javac.tree.JCTree.JCIdent;
import static com.sun.tools.javac.tree.JCTree.JCIf;
import static com.sun.tools.javac.tree.JCTree.JCLiteral;
import static com.sun.tools.javac.tree.JCTree.JCNewClass;
import static com.sun.tools.javac.tree.JCTree.JCReturn;
import static com.sun.tools.javac.tree.JCTree.JCStatement;
import static com.sun.tools.javac.tree.JCTree.JCThrow;
import static com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import static com.sun.tools.javac.tree.JCTree.Tag;
import static org.jmlspecs.openjml.JmlTree.JmlBlock;
import static org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import static org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import static org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import static org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import static org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import static org.jmlspecs.openjml.JmlTree.JmlStatementSpec;
import static org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import static org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword;
import static org.jmlspecs.openjml.JmlTree.Maker;
import static translation.VerifyFunctionVisitor.TranslationMode.ASSUME;

import cli.CLI;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import exceptions.TranslationException;
import exceptions.UnsupportedException;
import java.util.LinkedHashMap;
import java.util.stream.Collectors;
import javax.lang.model.element.Modifier;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeUtils;
import utils.NormalizeVisitor;
import utils.TranslationUtils;

/**
 * Created by jklamroth on 12/10/18.
 *
 * <p>
 * This visitor is used to create the second form of a specified method which is used
 * if this method is invoked. It mainly asserts the precondition and assumes the postcondition.
 * </p>
 */
public class SymbFunctionVisitor extends JmlTreeCopier {
    private final Maker maker;
    private final Context context;
    private final Symtab syms;
    private final JmlTreeUtils treeutils;
    private final ClassReader reader;
    private final BaseVisitor baseVisitor;
    private JmlMethodDecl currentMethod;
    private List<JCStatement> newStatements = List.nil();
    private List<JCStatement> combinedNewReqStatements = List.nil();
    private List<JCStatement> combinedNewEnsStatements = List.nil();
    private List<List<JCStatement>> reqCases = List.nil();
    private List<List<JCStatement>> ensCases = List.nil();
    private Symbol returnVar = null;
    private boolean hasReturn = false;
    private VerifyFunctionVisitor.TranslationMode translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
    private LinkedHashMap<JCExpression, JCVariableDecl> oldVars = new LinkedHashMap<>();
    private List<JCStatement> oldInits = List.nil();
    private List<JCExpression> currentAssignable = List.nil();
    private Symbol currentSymbol = null;
    private boolean inConstructor = false;

    public SymbFunctionVisitor(Context context, Maker maker, BaseVisitor base) {
        super(context, maker);
        baseVisitor = base;
        this.context = context;
        this.maker = Maker.instance(context);
        this.syms = Symtab.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
    }

    @Override
    public JCTree visitJmlSpecificationCase(JmlSpecificationCase that, Void p) {
        combinedNewEnsStatements = List.nil();
        combinedNewReqStatements = List.nil();
        JCTree copy = super.visitJmlSpecificationCase(that, p);

        if (TranslationUtils.isPure(currentMethod)) {
            currentAssignable = currentAssignable.append(maker.JmlStoreRefKeyword(JmlTokenKind.BSNOTHING));
        }

        reqCases = reqCases.append(combinedNewReqStatements);
        ensCases = ensCases.append(combinedNewEnsStatements);
        combinedNewEnsStatements = List.nil();
        combinedNewReqStatements = List.nil();
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseExpr(JmlMethodClauseExpr that, Void p) {
        TranslationUtils.setCurrentASTNode(that);
        //JmlMethodClauseExpr copy = (JmlMethodClauseExpr)super.visitJmlMethodClauseExpr(that, p);
        JmlExpressionVisitor expressionVisitor =
            new JmlExpressionVisitor(context, maker, baseVisitor, translationMode, oldVars, returnVar, currentMethod);
        if (that.clauseKind.name().equals("ensures")) {
            expressionVisitor.setTranslationMode(ASSUME);
            translationMode = ASSUME;
        } else if (that.clauseKind.name().equals("requires")) {
            expressionVisitor.setTranslationMode(VerifyFunctionVisitor.TranslationMode.ASSERT);
            translationMode = VerifyFunctionVisitor.TranslationMode.ASSERT;
        }
        expressionVisitor.inConstructor = this.inConstructor;
        JCExpression normalized = NormalizeVisitor.normalize(that.expression, context, maker);

        JCExpression copy = expressionVisitor.copy(normalized);
        newStatements = expressionVisitor.getNewStatements();
        newStatements = newStatements.prependList(expressionVisitor.getNeededVariableDefs());
        oldVars = expressionVisitor.getOldVars();
        oldInits = expressionVisitor.getOldInits();
        if (translationMode == ASSUME) {
            newStatements = newStatements.append(TranslationUtils.makeAssumeStatement(copy));
            combinedNewEnsStatements = combinedNewEnsStatements.appendList(newStatements);
        } else if (translationMode == VerifyFunctionVisitor.TranslationMode.ASSERT) {
            JCStatement st = TranslationUtils.makeAssertStatement(copy);
            if (st instanceof JmlBlock) {
                newStatements = newStatements.appendList(((JmlBlock) st).stats);
            } else {
                newStatements = newStatements.append(TranslationUtils.makeAssertStatement(copy));
            }
            combinedNewReqStatements = combinedNewReqStatements.appendList(newStatements);
        }
        newStatements = List.nil();
        translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        return maker.JmlMethodClauseExpr(that.clauseKind.name(), that.clauseKind, copy);
    }

    @Override
    public JCTree visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that, Void p) {
        currentAssignable = currentAssignable.appendList(that.list);
        return super.visitJmlMethodClauseStoreRef(that, p);
    }

    @Override
    public JCTree visitJmlStatementSpec(JmlStatementSpec that, Void p) {
        return that;
    }

    @Override
    public JCTree visitJmlMethodDecl(JmlMethodDecl that, Void p) {
        currentSymbol = that.sym;
        currentAssignable = List.nil();
        currentMethod = (JmlMethodDecl) that.clone();
        hasReturn = false;

        if (that.cases == null && !TranslationUtils.isPure(that)) {
            JmlMethodDecl copy = (JmlMethodDecl) visitJmlMethodDeclBugfix(that, p);
            copy.name = maker.Name(copy.name.toString() + "Symb");
            copy.mods.annotations = List.nil();
            if (copy.mods.getFlags().contains(Modifier.ABSTRACT)) {
                copy.mods.flags &= 1024;
            }
            if (that.getName().toString().equals("<init>")) {
                List<JCExpression> l = List.nil();
                for (JCVariableDecl vd : currentMethod.params) {
                    l = l.append(maker.Ident(vd));
                }
                JCReturn ret = maker.Return(
                    maker.NewClass(null, null, maker.at(TranslationUtils.getCurrentPosition()).Type(currentSymbol.owner.type), l, null));
                copy.body = maker.Block(0L, List.of(ret));
                copy.restype = maker.Ident(copy.sym.owner.name);
                copy.name = maker.Name(copy.sym.owner.name + "Symb");
                //Make it static
                copy.mods.flags |= 8L;
                //Make it public
                copy.mods.flags |= 1L;
                //Make it not private and not protected
                copy.mods.flags &= (~2L);
                copy.mods.flags &= (~4L);
            }
            return copy;
        }
        currentSymbol = that.sym;
        currentAssignable = List.nil();
        currentMethod = (JmlMethodDecl) that.clone();
        hasReturn = false;

        JCVariableDecl returnVar = null;
        Type t = that.sym.getReturnType();

        if (!(t instanceof Type.JCVoidType)) {
            returnVar =
                treeutils.makeVarDef(t, maker.Name("returnVar"), currentMethod.sym, TranslationUtils.getNondetFunctionForType(t, currentMethod.sym));
            hasReturn = true;
            this.returnVar = returnVar.sym;
        } else if (that.name.toString().equals("<init>")) {
            this.inConstructor = true;
            List<JCExpression> l = List.nil();
            for (JCVariableDecl vd : currentMethod.params) {
                l = l.append(maker.Ident(vd));
            }
            JCNewClass initVal = maker.NewClass(null, null, maker.at(TranslationUtils.getCurrentPosition()).Type(currentSymbol.owner.type), l, null);
            returnVar = treeutils.makeVarDef(currentMethod.sym.owner.type, maker.Name("returnVar"), currentMethod.sym, initVal);
            hasReturn = true;
            this.returnVar = returnVar.sym;
        } else {
            this.returnVar = null;
        }

        if (that.name.toString().equals("<init>")) {
            inConstructor = true;
        }
        JmlMethodDecl copy = (JmlMethodDecl) visitJmlMethodDeclBugfix(that, p);
        if (copy.name.toString().equals("<init>")) {
            copy.mods.flags &= 8L;
            copy.restype = maker.Ident(copy.sym.owner.name);
            inConstructor = false;
        }

        List<JCStatement> bodyStats = List.nil();
        for (JCVariableDecl variableDecl : oldVars.values()) {
            bodyStats = bodyStats.append(variableDecl);
        }

        for (JCStatement oldInit : oldInits) {
            bodyStats = bodyStats.append(oldInit);
        }

        if (CLI.proofPreconditions) {
            bodyStats = copy.body.stats;
        } else {
            if (currentAssignable.size() == 0 && !that.name.toString().equals("<init>")) {
                throw new UnsupportedException("Havocing \\everything is not supported. For invoked method: " + that.name);
            }
            bodyStats = bodyStats.appendList(TranslationUtils.havoc(currentAssignable, copy.sym, this));
        }

        List<JCStatement> l = List.nil();
        List<JCExpression> asserts = List.nil();
        if (reqCases.size() > 1) {
            JCExpression reqExpr = maker.Literal(false);
            for (int i = 0; i < reqCases.size(); ++i) {
                JCExpression innerReqExpr = maker.Literal(true);
                for (int j = 0; j < reqCases.get(i).size(); ++j) {
                    if (reqCases.get(i).get(j) instanceof JCAssert) {
                        JCAssert assertStmt = (JCAssert) reqCases.get(i).get(j);
                        innerReqExpr = treeutils.makeAnd(TranslationUtils.getCurrentPosition(), innerReqExpr, assertStmt.cond);
                    } else {
                        l = l.append(reqCases.get(i).get(j));
                    }
                }
                reqExpr = treeutils.makeOr(TranslationUtils.getCurrentPosition(), reqExpr, innerReqExpr);
                asserts = asserts.append(innerReqExpr);
            }
            l = l.append(TranslationUtils.makeAssertStatement(reqExpr));
        } else if (reqCases.size() == 1) {
            l = l.appendList(reqCases.get(0));
        }

        if (hasReturn && returnVar != null && !CLI.proofPreconditions) {
            l = l.append(returnVar);
        }
        l = l.appendList(bodyStats);

        if (!CLI.proofPreconditions) {
            if (ensCases.size() > 1) {
                for (int i = 0; i < ensCases.size(); ++i) {
                    JCExpression innerReqExpr = maker.Literal(true);
                    for (int j = 0; j < ensCases.get(i).size(); ++j) {
                        JCExpression expr = TranslationUtils.extractAssumeExpr(ensCases.get(i).get(j));
                        if (expr != null) {
                            innerReqExpr = treeutils.makeAnd(TranslationUtils.getCurrentPosition(), innerReqExpr, expr);
                        } else {
                            l = l.append(ensCases.get(i).get(j));
                        }
                    }
                    JCIf ifstmt = maker.If(asserts.get(i), TranslationUtils.makeAssumeStatement(innerReqExpr), null);
                    l = l.append(ifstmt);
                }
            } else if (ensCases.size() == 1) {
                l = l.appendList(ensCases.get(0));
            }
        }

        if (copy.name.toString().equals("<init>")) {
            l = l.append(TranslationUtils.makeAssumeOrAssertStatement(
                treeutils.makeNeqObject(TranslationUtils.getCurrentPosition(), maker.Ident(returnVar),
                    treeutils.makeNullLiteral(TranslationUtils.getCurrentPosition())), ASSUME));
        }
        if (hasReturn && returnVar != null && !CLI.proofPreconditions) {
            JCReturn returnStmt = maker.Return(maker.Ident(returnVar));
            l = l.append(returnStmt);
        }
        copy.body = maker.Block(0L, l);

        copy.methodSpecsCombined = null;
        copy.cases = null;
        if (copy.name.toString().equals("<init>")) {
            copy.name = maker.Name(copy.sym.owner.name + "Symb");
            //Make it static
            copy.mods.flags |= 8L;
            //Make it public
            copy.mods.flags |= 1L;
            //Make it not private and not protected
            copy.mods.flags &= (~2L);
            copy.mods.flags &= (~4L);
        } else {
            copy.name = maker.Name(currentMethod.name.toString() + "Symb");
        }
        copy.mods.annotations = List.nil();
        combinedNewReqStatements = List.nil();
        combinedNewEnsStatements = List.nil();
        if (copy.mods.getFlags().contains(Modifier.ABSTRACT)) {
            copy.mods.flags ^= 1024;
        }
        inConstructor = false;
        return copy;
    }

    public JCTree visitJmlMethodDeclBugfix(JmlMethodDecl that, Void p) {
        JmlMethodDecl copy = (JmlMethodDecl) super.visitMethod(that, p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl;
        //copy.cases = (JmlMethodSpecs)this.copy((JCTree)that.cases, (Object)p);
        copy.methodSpecsCombined = JmlSpecs.copy(that.methodSpecsCombined, p, this);
        copy.cases = (JmlMethodSpecs) copy.methodSpecsCombined.cases.clone();
        copy.type = that.type;
        return copy;
    }

    private boolean isSuperType(Type base, Type sup) {
        if (base.equals(sup)) {
            return true;
        }
        if (!(base instanceof Type.ClassType) || !(sup instanceof Type.ClassType)) {
            return false;
        }
        Type.ClassType b = (Type.ClassType) base;
        return isSuperType(b.supertype_field, sup);
    }
}
