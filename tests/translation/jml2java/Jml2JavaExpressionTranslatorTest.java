package translation.jml2java;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.TypeSolverBuilder;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.yaml.snakeyaml.Yaml;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

class Jml2JavaExpressionTranslatorTest {
    public static Stream<Arguments> readExpressionTests() throws IOException {
        Yaml yaml = new Yaml();
        try (var fw = new FileReader("testRes/expr-translation-tests.yml")) {
            List<Map<String, String>> obj = yaml.load(fw);

            return obj.stream().map(
                    it -> {
                        var mode = TranslationMode.valueOf(it.getOrDefault("mode", TranslationMode.ASSERT.toString()));
                        return Arguments.of(it.get("input"), it.get("expected"), mode);
                    });
        }
    }


    static BlockStmt parent;

    static {
        var config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new TypeSolverBuilder().withCurrentJRE().build()));
        var jp = new JavaParser(config);
        CompilationUnit cu = jp.parse(" public class A { void foo() {} } ").getResult().get();
        parent = cu.getType(0).asClassOrInterfaceDeclaration()
                .getMethodsByName("foo").get(0).getBody().get();
    }

    @ParameterizedTest
    @MethodSource("readExpressionTests")
    void testTranslation(String expr, String expected, TranslationMode mode) {
        var e = StaticJavaParser.parseJmlExpression(expr);
        parent.addAndGetStatement(e);
        var r = Jml2JavaFacade.translate(e, mode);
        var actual = new BlockStmt(r.statements).toString() + "\n" + r.value;
        Assertions.assertEquals(expected.trim(), actual);
    }
}