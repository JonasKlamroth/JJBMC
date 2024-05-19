package translation.jml2java;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.TypeSolverBuilder;
import com.github.javaparser.utils.SourceRoot;
import com.google.common.truth.Truth;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.yaml.snakeyaml.Yaml;

import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

class Jml2JavaExpressionTranslatorTest {
    private static final Path source = Paths.get("testRes/unit-tests/input").toAbsolutePath();
    private static final Path expectedSources = Paths.get("testRes/unit-tests/expected").toAbsolutePath();
    private static final Path actualSources = Paths.get("testRes/unit-tests/actual").toAbsolutePath();

    static {
        // Using an own JavaParser to configure a SymbolSolver. This is necessary, because for type resolution
        // of an expression, it is required that a symbolsolver is reachable.

        var config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new TypeSolverBuilder().withCurrentJRE().build()));
        var jp = new JavaParser(config);
        CompilationUnit cu = jp.parse(" public class A { void foo() {} } ").getResult().get();
        parent = cu.getType(0).asClassOrInterfaceDeclaration()
                .getMethodsByName("foo").get(0).getBody().get();
    }

    public static Stream<Arguments> readExpressionTests() throws IOException {
        Yaml yaml = new Yaml();
        try (var fw = new FileReader("testRes/unit-tests/expr-translation-tests.yml")) {
            List<Map<String, String>> obj = yaml.load(fw);

            return obj.stream().map(
                    it -> {
                        var mode = TranslationMode.valueOf(it.getOrDefault("mode", TranslationMode.ASSERT.toString()));
                        return Arguments.of(it.get("input"), it.get("expected"), mode);
                    });
        }
    }


    static BlockStmt parent;

    public static Stream<Arguments> findCompleteTranslationTests() throws IOException {
        var config = new ParserConfiguration();
        config.setProcessJml(true);
        config.setJmlKeys(Collections.singletonList(Collections.singletonList("jjbmc")));

        config.setSymbolResolver(new JavaSymbolSolver(
                new TypeSolverBuilder()
                        .withSourceCode(source)
                        .withCurrentJRE()
                        .build()));

        SourceRoot sourceRoot = new SourceRoot(source, config);
        return sourceRoot.tryToParse().stream().map(Arguments::of);
    }

    @ParameterizedTest
    @MethodSource("findCompleteTranslationTests")
    void testTranslation(ParseResult<CompilationUnit> check) throws IOException {
        if (!check.isSuccessful()) {
            check.getProblems().forEach(System.err::println);
            Assertions.fail("Error during parsing");
        }

        var cu = check.getResult().get();
        var actual = Jml2JavaFacade.translate(cu);
        System.out.println(actual);

        final var originalPath = cu.getStorage().get().getPath().toAbsolutePath();
        var path = expectedSources.resolve(
                source.relativize(originalPath));

        System.out.println(path);
        final var text = Jml2JavaFacade.pprint(actual);


        final var tmp = actualSources.resolve(source.relativize(originalPath));
        Files.createDirectories(tmp.getParent());
        Files.writeString(tmp, text);
        Assertions.assertEquals(Files.readString(path), text);
    }

    @ParameterizedTest
    @MethodSource("readExpressionTests")
    void testTranslation(String expr, String expected, TranslationMode mode) {
        var e = StaticJavaParser.parseJmlExpression(expr);
        parent.addAndGetStatement(e);
        var r = Jml2JavaFacade.translate(e, mode);
        var actual = new BlockStmt(r.statements) + "\n" + r.value;
        Truth.assertThat(actual.replaceAll("\\s+", " ").trim())
                .isEqualTo(expected.replaceAll("\\s+", " ").trim());
    }
}