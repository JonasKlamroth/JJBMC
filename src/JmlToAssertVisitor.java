import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.ReturnTree;
import com.sun.source.tree.Tree;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
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
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

/* Standard Java flags.
     */
//public static final int PUBLIC       = 1<<0;
//public static final int PRIVATE      = 1<<1;
//public static final int PROTECTED    = 1<<2;
//public static final int STATIC       = 1<<3;
//public static final int FINAL        = 1<<4;
//public static final int SYNCHRONIZED = 1<<5;
//public static final int VOLATILE     = 1<<6;
//public static final int TRANSIENT    = 1<<7;
//public static final int NATIVE       = 1<<8;
//public static final int INTERFACE    = 1<<9;
//public static final int ABSTRACT     = 1<<10;
//public static final int STRICTFP     = 1<<11;

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
    private LinkedList<JCTree.JCStatement> combinedNewReqStatements = new LinkedList<>();
    private LinkedList<JCTree.JCStatement> combinedNewEnsStatements = new LinkedList<>();
    private Symbol returnBool = null;
    private Symbol returnVar = null;
    private boolean hasReturn = false;
    private JCTree.JCClassDecl returnExcClass;
    private List<Object> visited = new ArrayList<>();
    private TranslationMode translationMode = TranslationMode.JAVA;

    public enum TranslationMode { REQUIRES, ENSURES, JAVA}

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
        if(that.token == JmlTokenKind.ENSURES) {
            translationMode = TranslationMode.ENSURES;
        } else if(that.token == JmlTokenKind.REQUIRES) {
            translationMode = TranslationMode.REQUIRES;
        }
        JCTree copy = super.visitJmlMethodClauseExpr(that, p);
        if(translationMode == TranslationMode.ENSURES) {
            if(returnBool != null) {
                newStatements.add(M.at(currentMethod.body.pos).Assert(M.Ident(returnBool), null));
            }
            combinedNewEnsStatements.addAll(newStatements);
        } else if(translationMode == TranslationMode.REQUIRES){
            if(returnBool != null) {
                JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
                JCTree.JCFieldAccess assumeFunc = M.Select(classCProver, M.Name("assume"));
                JCTree.JCExpression args[] = new JCTree.JCExpression[]{M.Ident(returnBool)};
                com.sun.tools.javac.util.List<JCTree.JCExpression> largs = com.sun.tools.javac.util.List.from(args);
                newStatements.add(M.Exec(
                        M.Apply(com.sun.tools.javac.util.List.nil(), assumeFunc, largs)));
            }
            combinedNewReqStatements.addAll(newStatements);
        }
        newStatements.clear();
        translationMode = TranslationMode.JAVA;
        return copy;
    }

    @Override
    public JCTree visitJmlMethodDecl(JmlTree.JmlMethodDecl that, Void p) {
        requiresList.clear();
        ensuresList.clear();
        currentMethod = that;
        hasReturn = false;
        JCTree.JCVariableDecl returnVar = null;
        Type t = ((JmlTree.JmlMethodDecl) that).sym.getReturnType();
        if(!(t instanceof Type.JCVoidType)) {
            returnVar = treeutils.makeVarDef(t, M.Name("returnVar"), currentMethod.sym, Position.NOPOS);
            this.returnVar = returnVar.sym;
        } else {
            this.returnVar = null;
        }
        JmlTree.JmlMethodDecl copy = (JmlTree.JmlMethodDecl)super.visitJmlMethodDecl(that, p);
        JCTree.JCVariableDecl catchVar = treeutils.makeVarDef(syms.exceptionType, M.Name("e"), currentMethod.sym, Position.NOPOS);
        JCTree.JCExpression ty = M.at(that).Type(syms.exceptionType);
        JCTree.JCExpression msg = treeutils.makeStringLiteral(that.pos, "Specification is not well defined for method " + that.getName());
        JCTree.JCThrow throwStmt = M.Throw(M.NewClass(null, null, ty, com.sun.tools.javac.util.List.of(msg), null));
        JCTree.JCTry reqTry = M.Try(M.Block(0L, com.sun.tools.javac.util.List.from(combinedNewReqStatements)),
                com.sun.tools.javac.util.List.of(M.Catch(catchVar, M.Block(0L, com.sun.tools.javac.util.List.of(throwStmt)))), null);
        JCTree.JCTry ensTry = M.Try(M.Block(0L, com.sun.tools.javac.util.List.from(combinedNewEnsStatements)),
                com.sun.tools.javac.util.List.of(M.Catch(catchVar, M.Block(0L, com.sun.tools.javac.util.List.of(throwStmt)))), null);

        JCTree.JCVariableDecl catchVarb = treeutils.makeVarDef(returnExcClass.type, M.Name("ex"), currentMethod.sym, Position.NOPOS);

        com.sun.tools.javac.util.List< JCTree.JCStatement> l = com.sun.tools.javac.util.List.nil();
        if(hasReturn) {
            if(returnVar != null) {
                com.sun.tools.javac.util.List< JCTree.JCStatement> l1 = com.sun.tools.javac.util.List.nil();
                JCTree.JCReturn returnStmt = M.Return(M.Ident(returnVar));
                if(combinedNewEnsStatements.size() > 0) {
                    l1 = l1.append(ensTry);
                }
                l1 = l1.append(returnStmt);
                JCTree.JCTry bodyTry = M.Try(M.Block(0L, copy.body.getStatements()),
                        com.sun.tools.javac.util.List.of(
                                M.Catch(catchVarb, M.Block(0L, l1))
                        ),
                        null);
                if(combinedNewReqStatements.size() > 0) {
                    l = l.append(reqTry);
                }
                l = l.append(returnVar).append(bodyTry);
            } else {
                if(combinedNewEnsStatements.size() > 0) {
                    JCTree.JCTry bodyTry = M.Try(M.Block(0L, copy.body.getStatements()),
                            com.sun.tools.javac.util.List.of(
                                    M.Catch(catchVarb, M.Block(0L, com.sun.tools.javac.util.List.of(ensTry)))
                            ),
                            null);
                    l = l.append(reqTry).append(bodyTry);
                } else {
                    l = copy.body.getStatements();
                }
            }
        } else {
            l = copy.body.getStatements();
            if(combinedNewEnsStatements.size() > 0) {
                l = l.append(ensTry);
            }
            if(combinedNewReqStatements.size() > 0) {
                l = l.prepend(reqTry);
            }
        }
        currentMethod.body = M.Block(0L, l);

        currentMethod.methodSpecsCombined = null;
        currentMethod.cases = null;
        combinedNewReqStatements.clear();
        combinedNewEnsStatements.clear();
        return currentMethod;
    }

    @Override
    public JCTree visitJmlCompilationUnit(JmlTree.JmlCompilationUnit that, Void p) {
        JmlTree.JmlCompilationUnit cu = (JmlTree.JmlCompilationUnit) super.visitJmlCompilationUnit(that, p);
        cu.defs = cu.defs.prepend(M.Import(M.Ident(M.Name("org.cprover.CProver")), false));
        return cu;
    }

    @Override
    public JCTree visitJmlClassDecl(JmlTree.JmlClassDecl that, Void p) {
        Symbol.ClassSymbol classSymbol = reader.defineClass(M.Name("ReturnException"), that.sym);
        classSymbol.sourcefile = that.sourcefile;
        classSymbol.completer = null;
        classSymbol.flatname = M.Name("ReturnException");
        returnExcClass = M.ClassDef(M.Modifiers(8L), M.Name("ReturnException"), com.sun.tools.javac.util.List.nil(),
                M.Type(syms.runtimeExceptionType),
                com.sun.tools.javac.util.List.nil(),
                com.sun.tools.javac.util.List.nil());
        returnExcClass.sym = classSymbol;
        returnExcClass.type = classSymbol.type;
        JmlTree.JmlClassDecl copy = (JmlTree.JmlClassDecl)super.visitJmlClassDecl(that, p);
        copy.defs = copy.defs.append(returnExcClass);
        return copy;
    }

    @Override
    public JCTree visitJmlQuantifiedExpr(JmlTree.JmlQuantifiedExpr that, Void p) {
        if(!visited.contains(that)) {
            JmlTree.JmlQuantifiedExpr copy = that;
            visited.add(that);

            if(translationMode == TranslationMode.ENSURES) {
                if(copy.op == JmlTokenKind.BSFORALL) {
                    JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
                    JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetInt"));
                    com.sun.tools.javac.util.List<JCTree.JCExpression> largs = com.sun.tools.javac.util.List.nil();
                    JCTree.JCVariableDecl quantVar = treeutils.makeVarDef(syms.intType, names.fromString(that.decls.get(0).getName().toString()), currentMethod.sym, M.Apply(com.sun.tools.javac.util.List.nil(), nondetFunc, largs));
                    newStatements.addLast(quantVar);
                    super.copy(copy.value);
                    return M.Ident(returnBool);
                } else if(copy.op == JmlTokenKind.BSEXISTS) {
                    super.copy(copy.value);
                    JCTree.JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentMethod.sym, treeutils.makeLit(Position.NOPOS, syms.booleanType, false));
                    JCTree.JCBinary b = M.Binary(JCTree.Tag.OR, M.Ident(boolVar), M.Ident(returnBool));
                    newStatements.addLast(M.Exec(M.Assign(M.Ident(boolVar), b)));
                    LinkedList<JCTree.JCStatement> l = new LinkedList<>();
                    l.add(boolVar);
                    l.add(makeStandardLoop(copy.range, newStatements, that.decls.get(0).getName().toString()));
                    newStatements = l;
                    returnBool = boolVar.sym;
                    return M.Ident(boolVar);
                }
            } else if(translationMode == TranslationMode.REQUIRES) {
                if(copy.op == JmlTokenKind.BSFORALL) {
                    super.copy(copy.value);
                    JCTree.JCVariableDecl boolVar = treeutils.makeVarDef(syms.booleanType, names.fromString("b_" + boolVarCounter++), currentMethod.sym, treeutils.makeLit(Position.NOPOS, syms.booleanType, false));
                    JCTree.JCBinary b = M.Binary(JCTree.Tag.AND, M.Ident(boolVar), M.Ident(returnBool));
                    newStatements.addLast(M.Exec(M.Assign(M.Ident(boolVar), b)));
                    LinkedList<JCTree.JCStatement> l = new LinkedList<>();
                    l.add(boolVar);
                    l.add(makeStandardLoop(copy.range, newStatements, that.decls.get(0).getName().toString()));
                    newStatements = l;
                    returnBool = boolVar.sym;
                    return M.Ident(boolVar);
                } else if(copy.op == JmlTokenKind.BSEXISTS) {
                    JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
                    JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetInt"));
                    com.sun.tools.javac.util.List<JCTree.JCExpression> largs = com.sun.tools.javac.util.List.nil();
                    JCTree.JCVariableDecl quantVar = treeutils.makeVarDef(syms.intType, names.fromString(that.decls.get(0).getName().toString()), currentMethod.sym, M.Apply(com.sun.tools.javac.util.List.nil(), nondetFunc, largs));
                    newStatements.addLast(quantVar);
                    super.copy(copy.value);
                    return M.Ident(returnBool);
                }
            }

            return copy;
        }
        return that;
    }

    @Override
    public JCTree visitBinary(BinaryTree node, Void p) {
        if(!visited.contains(node) && translationMode != TranslationMode.JAVA) {
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
        if(!visited.contains(node) && translationMode != TranslationMode.JAVA) {
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

    @Override
    public JCTree visitReturn(ReturnTree node, Void p) {
        hasReturn = true;
        JCTree.JCReturn copy = (JCTree.JCReturn)super.visitReturn(node, p);
        JCTree.JCAssign assign = null;
        if(returnVar != null) {
            assign = M.Assign(M.Ident(returnVar), copy.getExpression());
        }
        JCTree.JCExpression ty = M.at(copy).Type(returnExcClass.type);
        JCTree.JCThrow throwStmt = M.Throw(M.NewClass(null, null, ty, com.sun.tools.javac.util.List.nil(), null));
        if(assign != null) {
            JCTree.JCBlock block = M.Block(0L, com.sun.tools.javac.util.List.of(M.Exec(assign), throwStmt));
            return block;
        } else {
            JCTree.JCBlock block = M.Block(0L, com.sun.tools.javac.util.List.of(throwStmt));
            return block;
        }
    }

    private JCTree.JCExpression makeRangeCondition(int min, int max, Symbol loopVar) {
        JCTree.JCBinary lower = M.Binary(JCTree.Tag.LT, M.Literal(min), M.Ident(loopVar));
        JCTree.JCBinary upper = M.Binary(JCTree.Tag.GT, M.Literal(max), M.Ident(loopVar));
        return M.Binary(JCTree.Tag.AND, lower, upper);
    }

    private JCTree.JCStatement makeStandardLoop(JCTree.JCExpression range, List<JCTree.JCStatement> body, String loopVarName) {
        JCTree.JCVariableDecl loopVar = treeutils.makeVarDef(syms.intType, names.fromString(loopVarName), currentMethod.sym, treeutils.makeLit(Position.NOPOS, syms.intType, 0));
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