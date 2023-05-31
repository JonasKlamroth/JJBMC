package cli;

import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.printer.DefaultPrettyPrinterVisitor;
import com.github.javaparser.printer.SourcePrinter;
import com.github.javaparser.printer.configuration.PrinterConfiguration;

/**
 * Fixes an error in JavaParser pretty printing of JML-contracts
 * Delete on newer versions.
 */
public class MyPPrintVisitor extends DefaultPrettyPrinterVisitor {
    public MyPPrintVisitor(PrinterConfiguration configuration) {
        super(configuration);
    }

    public MyPPrintVisitor(PrinterConfiguration configuration, SourcePrinter printer) {
        super(configuration, printer);
    }

    @Override
    public void visit(JmlContract n, Void arg) {
        printer.print("/*@");
        super.visit(n, arg);
        printer.print("*/");
    }
}
