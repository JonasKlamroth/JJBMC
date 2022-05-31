package cli;

import java.util.HashSet;
import java.util.Set;
import org.apache.logging.log4j.LogManager;

public class ErrorLogger {
    private static final org.apache.logging.log4j.Logger log = LogManager.getLogger(ErrorLogger.class);
    private static final Set<String> errors = new HashSet<>();

    public static void debug(String msg) {
        if (!errors.contains(msg)) {
            errors.add(msg);
            log.debug(msg);
        }
    }

    public static void info(String msg) {
        if (!errors.contains(msg)) {
            errors.add(msg);
            log.info(msg);
        }
    }

    public static void fatal(String msg) {
        if (!errors.contains(msg)) {
            errors.add(msg);
            log.fatal(msg);
        }
    }

    public static void error(String msg) {
        if (!errors.contains(msg)) {
            errors.add(msg);
            log.error(msg);
        }
    }

    public static void trace(String msg) {
        if (!errors.contains(msg)) {
            errors.add(msg);
            log.trace(msg);
        }
    }

    public static void warn(String msg) {
        if (!errors.contains(msg)) {
            errors.add(msg);
            log.warn(msg);
        }
    }
}
