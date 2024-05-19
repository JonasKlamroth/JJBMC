package utils;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import jjbmc.FunctionNameVisitor.TestBehaviour;

import java.util.List;

public class TestOptionsListener extends VoidVisitorAdapter<List<TestOptionsListener.TestOptions>> {
    public record TestOptions(TestBehaviour behaviour, int unwinds, String functionName) {}
    @Override
    public void visit(MethodDeclaration n, List<TestOptions> testOptions) {
        TestOptions to = new TestOptions(TestBehaviour.Verifyable,
                5,
                n.resolve().getQualifiedName());
        testOptions.add(to);
    }
}
