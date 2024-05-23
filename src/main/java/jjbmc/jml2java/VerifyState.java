package jjbmc.jml2java;

import com.github.javaparser.ast.Node;

public class VerifyState {
    public static void verify(Node n) {
        for(Node c : n.getChildNodes()) {
            verify(c);
            if(c.getParentNode() == null || c.getParentNode().get() != n) {
                throw new IllegalStateException("Broken parent relation for node: " + c);
            }
        }
    }
}
