package translation;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import java.util.List;

public class FunctionNameVisitor extends VoidVisitorAdapter<List<String>> {
    @Override
    public void visit(MethodDeclaration n, List<String> functionNames) {
        functionNames.add(n.resolve().getQualifiedName());
    }
}
