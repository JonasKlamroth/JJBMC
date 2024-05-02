package utils;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import java.util.List;

public class TestOptionsListener extends VoidVisitorAdapter<List<TestOptionsListener.TestOptions>> {
    class TestOptions {
        public TestBehaviour behaviour;
        public int unwinds;
        public String functionName;

        public TestOptions(TestBehaviour behaviour, int unwinds, String functionName) {
            this.behaviour = behaviour;
            this.unwinds = unwinds;
            this.functionName = functionName;
        }
    }
    @Override
    public void visit(MethodDeclaration n, List<TestOptions> testOptions) {
        TestOptions to = new TestOptions(TestBehaviour.Verifiable,
                5,
                n.resolve().getQualifiedName());
        testOptions.add(to);
    }
}

