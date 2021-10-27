import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class CaseStudies {
    private String configString = null;
    private Path configFilePath = new File("testRes/CaseStudyConfig.json").toPath();
    private JsonObject configs = null;
    private Logger log = LogManager.getLogger(CaseStudies.class);

    @Test
    public void runCaseStudies() throws Exception {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
        File caseStudyFolder = new File("testRes/CaseStudy");
        for(File f : caseStudyFolder.listFiles()) {
            if (f.isFile()) {
                for(List<String> l : getConfigsForFile(f.getName())) {
                    l.add(0, f.getAbsolutePath());
                    l.add(0, "-c");
                    String[] args = new String[l.size()];
                    args = l.toArray(args);
                    log.info("Running Casestudy: " + f.getName());
                    log.info("with params: " + Arrays.toString(args));
                    Main.main(args);
                }
            }
        }
    }

    public List<List<String>> getConfigsForFile(String file) {
        if(configString == null) {
            readConfigString();
            JsonParser parser = new JsonParser();
            configs = (JsonObject) parser.parse(configString);
        }
        JsonArray config = (JsonArray) configs.get(file);
        if(config == null) {
            List<String> innerList = new ArrayList<>();
            List<List<String>> outerList = new ArrayList<>();
            outerList.add(innerList);
            return outerList;
        }
        return jsonToList(config);
    }

    private List<List<String>> jsonToList(JsonArray arr) {
        List<List<String>> configs = new ArrayList<>();
        for(int i = 0; i < arr.size(); ++i) {
            List<String> config = new ArrayList<>();
            JsonArray jsonConfig = (JsonArray) arr.get(i);
            for(int j = 0; j < jsonConfig.size(); ++j) {
                config.add(jsonConfig.get(j).getAsString());
            }
            configs.add(config);
        }
        return configs;
    }

    private void readConfigString() {
        try {
            configString = String.join("\n", Files.readAllLines(configFilePath));
        } catch (IOException e) {
            assert false;
        }
    }
}
