import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.LiteralTree;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;

import java.util.HashMap;
import java.util.Map;

import static com.sun.tools.javac.tree.JCTree.JCBinary;
import static com.sun.tools.javac.tree.JCTree.JCExpression;
import static com.sun.tools.javac.tree.JCTree.JCIdent;
import static com.sun.tools.javac.tree.JCTree.JCLiteral;
import static com.sun.tools.javac.tree.JCTree.JCStatement;
import static com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import static com.sun.tools.javac.tree.JCTree.Tag;
import static org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import static org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import static org.jmlspecs.openjml.JmlTree.JmlSingleton;
import static org.jmlspecs.openjml.JmlTree.Maker;

/**
 * Created by jklamroth on 11/14/18.
 */
public class JmlExpressionVisitor extends JmlTreeCopier {
    private final Maker M;
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
    private final translationUtils transUtils;
    private final JmlAttr attr;
    private final Name resultName;
    private final Name exceptionName;
    private final Name exceptionNameCall;
    private final Name terminationName;
    private final ClassReader reader;
    private final Symbol.ClassSymbol utilsClass;
    private final JCIdent preLabel;
    private Symbol currentSymbol;
    private int boolVarCounter = 0;
    private List<JCStatement> newStatements = List.nil();
    private Symbol returnBool = null;
    private Symbol returnVar = null;
    private List<Object> visited = List.nil();
    private JmlToAssertVisitor.TranslationMode translationMode = JmlToAssertVisitor.TranslationMode.JAVA;
    private Map<Integer, JCVariableDecl> oldVars = new HashMap<>();
    private  final BaseVisitor baseVisitor;



    public JmlExpressionVisitor(Context context, Maker maker,
                                BaseVisitor base,
                                JmlToAssertVisitor.TranslationMode translationMode,
                                Map<Integer, JCVariableDecl> oldVars,
                                Symbol returnVar) {
        super(context, maker);
        baseVisitor = base;
        this.context = context;
        this.log = Log.instance(context);
        this.M = Maker.instance(context);
        this.names = Names.instance(context);
        this.nowarns = Nowarns.instance(context);
        this.syms = Symtab.instance(context);
        this.types = Types.instance(context);
        this.utils = Utils.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.jmltypes = JmlTypes.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        transUtils = new translationUtils(context, M);
        this.attr = JmlAttr.instance(context);
        this.resultName = names.fromString(Strings.resultVarString);
        this.exceptionName = names.fromString(Strings.exceptionVarString);
        this.exceptionNameCall = names.fromString(Strings.exceptionCallVarString);
        this.terminationName = names.fromString(Strings.terminationVarString);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
        this.utilsClass = reader.enterClass(names.fromString(Strings.runtimeUtilsFQName));
        this.preLabel = treeutils.makeIdent(Position.NOPOS, Strings.empty, syms.intType);
        this.translationMode = translationMode;
        this.oldVars = oldVars;
        this.returnVar = returnVar;
    }

    @Override
    public JCTree visitJmlQuantifiedExpr(JmlQuantifiedExpr that, Void p) {
        if(!visited.contains(that)) {
            JmlQuantifiedExpr copy = that;
            visited = visited.append(that);

            if(translationMode == JmlToAssertVisitor.TranslationMode.ENSURES) {
                if(copy.op == JmlTokenKind.BSFORALL) {
                    JCVariableDecl quantVar = transUtils.makeNondetInt(names.fromString(that.decls.get(0).getName().toString()), currentSymbol);
                    newStatements = newStatements.append(quantVar);
                    newStatements = newStatements.append(translationUtils.makeAssumeStatement(super.copy(copy.range), M));
                    JCExpression value = super.copy(copy.value);
                    return value;
                } else if(copy.op == JmlTokenKind.BSEXISTS) {
                    JCExpression value = super.copy(copy.value);
                    JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentSymbol, treeutils.makeLit(Position.NOPOS, syms.booleanType, false));
                    JCBinary b = M.Binary(Tag.OR, M.Ident(boolVar), value);
                    newStatements = newStatements.append(M.Exec(M.Assign(M.Ident(boolVar), b)));
                    List<JCStatement> l = List.nil();
                    l.append(boolVar);
                    l.append(transUtils.makeStandardLoop(copy.range, newStatements, that.decls.get(0).getName().toString(), currentSymbol));
                    newStatements = l;
                    returnBool = boolVar.sym;
                    return M.Ident(boolVar);
                }
            } else if(translationMode == JmlToAssertVisitor.TranslationMode.REQUIRES) {
                if(copy.op == JmlTokenKind.BSFORALL) {
                    JCExpression value = super.copy(copy.value);
                    JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentSymbol, treeutils.makeLit(Position.NOPOS, syms.booleanType, false));
                    JCBinary b = M.Binary(Tag.AND, M.Ident(boolVar), value);
                    newStatements = newStatements.append(M.Exec(M.Assign(M.Ident(boolVar), b)));
                    List<JCStatement> l = List.nil();
                    l.append(boolVar);
                    l.append(transUtils.makeStandardLoop(copy.range, newStatements, that.decls.get(0).getName().toString(), currentSymbol));
                    newStatements = l;
                    returnBool = boolVar.sym;
                    return M.Ident(boolVar);
                } else if(copy.op == JmlTokenKind.BSEXISTS) {
                    JCVariableDecl quantVar = transUtils.makeNondetInt(names.fromString(that.decls.get(0).getName().toString()), currentSymbol);
                    newStatements = newStatements.append(quantVar);
                    newStatements = newStatements.append(translationUtils.makeAssumeStatement(super.copy(copy.range), M));
                    JCExpression value = super.copy(copy.value);
                    return value;
                }
            }

            return copy;
        }
        return that;
    }

    @Override
    public JCTree visitBinary(BinaryTree node, Void p) {
        if(!visited.contains(node) && translationMode != JmlToAssertVisitor.TranslationMode.JAVA) {
            visited = visited.append(node);
            JCBinary copy = (JCBinary) super.visitBinary(node, p);
            if(copy.operator.asType().getReturnType() == syms.booleanType) {
                JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentSymbol, copy);
                //newStatements.append(boolVar);
                returnBool = boolVar.sym;
                return copy;
            }
        }
        return super.visitBinary(node, p);
    }

    @Override
    public JCTree visitLiteral(LiteralTree node, Void p) {
        if(!visited.contains(node) && translationMode != JmlToAssertVisitor.TranslationMode.JAVA) {
            visited = visited.append(node);
            JCLiteral copy = (JCLiteral) super.visitLiteral(node, p);
            if(copy.type.baseType() == syms.booleanType) {
                JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentSymbol, copy);
                newStatements = newStatements.append(boolVar);
                returnBool = boolVar.sym;
                return M.Ident(boolVar);
            }
        }
        return super.visitLiteral(node, p);
    }

    @Override
    public JCTree visitJmlMethodInvocation(JmlMethodInvocation that, Void p) {
        switch (that.token) {
            case BSOLD:
                JCExpression arg = that.getArguments().get(0);
                JCVariableDecl oldVar;
                if(arg instanceof JCIdent) {
                    if(!oldVars.keySet().contains(((JCIdent) arg).sym.hashCode())) {
                        if(arg.type instanceof Type.JCPrimitiveType) {
                            oldVar = treeutils.makeVarDef(arg.type, M.Name(String.valueOf("old" + arg.hashCode())), currentSymbol, arg);
                        } else {
                            oldVar = treeutils.makeVarDef(arg.type, M.Name(String.valueOf("old" + arg.hashCode())), currentSymbol,
                                    M.Apply(List.nil(),
                                            M.Select(arg, M.Name("clone")),
                                            List.nil()));
                        }
                        oldVars.put(((JCIdent) arg).sym.hashCode(), oldVar);
                    } else {
                        oldVar = oldVars.get(((JCIdent) arg).sym.hashCode());
                    }
                } else {
                    if(arg.type instanceof Type.JCPrimitiveType) {
                        oldVar = treeutils.makeVarDef(arg.type, M.Name(String.valueOf("old" + arg.hashCode())), currentSymbol, arg);
                    } else {
                        oldVar = treeutils.makeVarDef(arg.type, M.Name(String.valueOf("old" + arg.hashCode())), currentSymbol,
                                M.Apply(List.nil(),
                                        M.Select(arg, M.Name("clone")),
                                        List.nil()));
                    }
                    oldVars.put(arg.hashCode(), oldVar);
                }

                return M.Ident(oldVar);
            default:
                throw new RuntimeException("JmlMethodInvocation with type " + that.token + " is not supported.");
        }
    }

    @Override
    public JCTree visitJmlSingleton(JmlSingleton that, Void p) {
        switch (that.token) {
            case BSRESULT:
                return M.Ident(returnVar);
            default:
                throw new RuntimeException("JmlSingleton with type " + that.token + " is not supported.");
        }
    }

    public List<JCStatement> getNewStatements() {
        return newStatements;
    }

    public Symbol getReturnBool() {
        return returnBool;
    }

    public Map<Integer, JCVariableDecl> getOldVars() {
        return oldVars;
    }
}
