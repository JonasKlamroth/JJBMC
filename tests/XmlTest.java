import org.apache.logging.log4j.Logger;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.apache.logging.log4j.*;


import static org.junit.Assert.*;

public class XmlTest {

    @Test
    public void xmlTest1() {
        Logger log = LogManager.getLogger(CLI.class);
        CLI.runWithTrace = true;
        CLI.translateAndRunJBMC("./testRes/xmlTest/TmpTest.java");
    }

}