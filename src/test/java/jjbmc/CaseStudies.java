package jjbmc;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static jjbmc.ErrorLogger.info;

public class CaseStudies {
    private String configString = null;
    private final Path configFilePath = new File("testRes" + File.separator + "CaseStudyConfig.json").toPath();
    private JsonObject configs = null;

    public static void main(String[] args) {
        try {
            new CaseStudies().runCaseStudies();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    public void runCaseStudies() throws Exception {
        System.setErr(new CostumPrintStream(System.err));
        System.setOut(new CostumPrintStream(System.out));
        try (var walk = Files.walk(Paths.get("testRes", "CaseStudy"))) {
            var caseStudyFolder = walk
                    .filter(Files::isRegularFile)
                    .toList();
            for (var f : caseStudyFolder) {
                for (List<String> l : getConfigsForFile(f.getFileName().toString())) {
                    l.addFirst(f.toAbsolutePath().toString());
                    l.addFirst("-c");
                    var args = l.toArray(new String[0]);
                    info("Running Casestudy: %s", f.getFileName());
                    info("with params: " + Arrays.toString(args));
                    Main.main(args);
                }
            }
        }
    }

    public List<List<String>> getConfigsForFile(String file) {
        if (configString == null) {
            readConfigString();
            configs = (JsonObject) JsonParser.parseString(configString);
        }
        JsonArray config = (JsonArray) configs.get(file);
        if (config == null) {
            List<String> innerList = new ArrayList<>();
            List<List<String>> outerList = new ArrayList<>();
            outerList.add(innerList);
            return outerList;
        }
        return jsonToList(config);
    }

    private List<List<String>> jsonToList(JsonArray arr) {
        List<List<String>> configs = new ArrayList<>();
        for (int i = 0; i < arr.size(); ++i) {
            List<String> config = new ArrayList<>();
            JsonArray jsonConfig = (JsonArray) arr.get(i);
            for (int j = 0; j < jsonConfig.size(); ++j) {
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
