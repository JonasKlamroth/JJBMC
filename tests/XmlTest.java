import cli.CLI;
import java.io.File;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

import org.apache.logging.log4j.*;

public class XmlTest {

    @Test
    public void xmlTest1() {
        Logger log = LogManager.getLogger(CLI.class);
        CLI.runWithTrace = true;
        CLI.translateAndRunJBMC("." + File.separator + "testRes" + File.separator + "xmlTest" + File.separator + "TmpTest.java");
    }

}