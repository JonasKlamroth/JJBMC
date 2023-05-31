package test;


import org.junit.platform.launcher.Launcher;
import org.junit.platform.launcher.LauncherDiscoveryRequest;
import org.junit.platform.launcher.core.LauncherDiscoveryRequestBuilder;
import org.junit.platform.launcher.core.LauncherFactory;
import org.junit.platform.launcher.listeners.SummaryGeneratingListener;
import org.junit.platform.launcher.listeners.TestExecutionSummary;

import java.io.PrintWriter;

import static org.junit.platform.engine.discovery.ClassNameFilter.includeClassNamePatterns;
import static org.junit.platform.engine.discovery.DiscoverySelectors.selectPackage;

public class TestRunner {

    static SummaryGeneratingListener summaryGeneratingListener = new SummaryGeneratingListener();

    public static void main(String[] args) {
        LauncherDiscoveryRequest request = LauncherDiscoveryRequestBuilder.request()
            .selectors(selectPackage("test"))
            .selectors(selectPackage("traceTest"))
            .filters(includeClassNamePatterns(".*Tests"))
            .build();
        Launcher launcher = LauncherFactory.create();
        launcher.registerTestExecutionListeners(summaryGeneratingListener);
        launcher.execute(request);


        TestExecutionSummary summary = summaryGeneratingListener.getSummary();

        summaryGeneratingListener.getSummary().printFailuresTo(new PrintWriter(System.out));
        summary.printTo(new PrintWriter(System.out));

        if(summaryGeneratingListener.getSummary().getTestsFailedCount() > 0) {
            System.exit(1);
        }
    }


}
