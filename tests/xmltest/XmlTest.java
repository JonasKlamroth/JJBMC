package xmltest;

import cli.CLI;
import java.io.File;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

public class XmlTest {

    @Test
    public void xmlTest1() {
        Logger log = LogManager.getLogger(CLI.class);
        CLI.runWithTrace = true;
        CLI.translateAndRunJBMC("." + File.separator + "testRes" + File.separator + "xmlTest" + File.separator + "TmpTest.java");
    }

}