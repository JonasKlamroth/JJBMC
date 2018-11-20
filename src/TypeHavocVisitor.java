import com.sun.imageio.plugins.jpeg.JPEG;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.List;
import org.jmlspecs.openjml.JmlTree;

/**
 * Created by jklamroth on 11/16/18.
 */
public class TypeHavocVisitor implements Type.Visitor<JCTree.JCMethodInvocation, Void> {
    private final JmlTree.Maker M;

    public TypeHavocVisitor(JmlTree.Maker maker) {
        M = maker;
    }

    @Override
    public JCTree.JCMethodInvocation visitClassType(Type.ClassType classType, Void aVoid) {
        JCTree.JCIdent classCProver = M.Ident(M.Name("CProver"));
        JCTree.JCFieldAccess nondetFunc = M.Select(classCProver, M.Name("nondetWithNull"));
        List<JCTree.JCExpression> largs = List.nil();
        return M.Apply(List.nil(), nondetFunc, largs);
    }

    @Override
    public JCTree.JCMethodInvocation visitWildcardType(Type.WildcardType wildcardType, Void aVoid) {
        throw new RuntimeException("Not supported type.");
    }

    @Override
    public JCTree.JCMethodInvocation visitArrayType(Type.ArrayType arrayType, Void aVoid) {
        throw new RuntimeException("Not supported type.");
    }

    @Override
    public JCTree.JCMethodInvocation visitMethodType(Type.MethodType methodType, Void aVoid) {
        throw new RuntimeException("Not supported type.");
    }

    @Override
    public JCTree.JCMethodInvocation visitPackageType(Type.PackageType packageType, Void aVoid) {
        throw new RuntimeException("Not supported type.");
    }

    @Override
    public JCTree.JCMethodInvocation visitTypeVar(Type.TypeVar typeVar, Void aVoid) {
        throw new RuntimeException("Not supported type.");
    }

    @Override
    public JCTree.JCMethodInvocation visitCapturedType(Type.CapturedType capturedType, Void aVoid) {
        throw new RuntimeException("Not supported type.");
    }

    @Override
    public JCTree.JCMethodInvocation visitForAll(Type.ForAll forAll, Void aVoid) {
        throw new RuntimeException("Not supported type.");
    }

    @Override
    public JCTree.JCMethodInvocation visitUndetVar(Type.UndetVar undetVar, Void aVoid) {
        throw new RuntimeException("Not supported type.");
    }

    @Override
    public JCTree.JCMethodInvocation visitErrorType(Type.ErrorType errorType, Void aVoid) {
        throw new RuntimeException("Not supported type.");
    }

    @Override
    public JCTree.JCMethodInvocation visitAnnotatedType(Type.AnnotatedType annotatedType, Void aVoid) {
        throw new RuntimeException("Not supported type.");
    }

    @Override
    public JCTree.JCMethodInvocation visitType(Type type, Void aVoid) {
        throw new RuntimeException("Not supported type.");
    }

    public static <T> T nondetWithNull()
    {
        if (true)
        {
            throw new RuntimeException(
                    "Cannot execute program with CProver.nondetWithNull<T>(T)");
        }

        return null;
    }
}
