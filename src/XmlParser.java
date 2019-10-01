import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class XmlParser {

    private class Assignment {
        public int lineNumber;
        public String jbmcVarname;
        public String value;

        public Assignment(int line, String jbmcVarname, String value) {
            this.lineNumber = line;
            this.jbmcVarname = jbmcVarname;
            this.value = value;
        }

        public Assignment(String line, String jbmcVarname, String value) {
            this(Integer.parseInt(line), jbmcVarname, value);
        }
    }

    private List<Assignment> references = new ArrayList<>();
    private Map<String, String> varNameMap = new HashMap<>();

    public void parse(String filename, String sourceFile) {
        File f = new File(filename);
        File f1 = new File(sourceFile);
        List<String> lines = new ArrayList<>();
        try {
            lines = Files.readAllLines(f1.toPath());
        } catch (IOException e) {
            System.out.println("Error reading file: " + f1.getAbsolutePath());
        }
        try {
            DocumentBuilder dBuilder = DocumentBuilderFactory.newInstance().newDocumentBuilder();
            Document doc = dBuilder.parse(f);
            doc.getDocumentElement().normalize();
            NodeList propertyNodeList = doc.getElementsByTagName("result");
            for(int i = 0; i < propertyNodeList.getLength(); ++i) {
                Node propertyNode = propertyNodeList.item(i);
                if (propertyNode.getNodeType() == Node.ELEMENT_NODE) {
                    Element propertyElemnt = (Element) propertyNode;
                    if(propertyElemnt.getAttribute("status").equals("FAILURE")) {
                        Element failure = (Element)propertyElemnt.getElementsByTagName("failure").item(0);
                        Element location = (Element) failure.getElementsByTagName("location").item(0);
                        System.out.println("Property " + propertyElemnt.getAttribute("property") + " failed in line " + location.getAttribute("line") +
                                " for the following assignment:");
                        NodeList assignmentList = ((Element) propertyNode).getElementsByTagName("assignment");
                        for(int j = 0; j < assignmentList.getLength(); ++j) {
                            Element assignment = (Element)assignmentList.item(j);
                            if(assignment.getElementsByTagName("location").getLength() > 0) {
                                Element aLocation = (Element) assignment.getElementsByTagName("location").item(0);
                                Element lhs = (Element) assignment.getElementsByTagName("full_lhs").item(0);
                                Element value = (Element) assignment.getElementsByTagName("value").item(0);
                                String l = lines.get(Integer.parseInt(aLocation.getAttribute("line")) - 1);
                                if(assignment.getAttribute("hidden").equals("false") && lhs.getTextContent().contains("this") || lhs.getTextContent().contains("anonlocal") || lhs.getTextContent().contains("arg")) {
                                    Pattern p = Pattern.compile("(\\w*) ?= ?\\w*;");
                                    Matcher m = p.matcher(l);
                                    String guess = "null";
                                    if(m.find()) {
                                        guess = m.group(1);
                                        references.add(new Assignment(aLocation.getAttribute("line"), lhs.getTextContent(), value.getTextContent()));
                                        if(varNameMap.containsKey(lhs.getTextContent()) && !varNameMap.get(lhs.getTextContent()).equals(guess)) {
                                            System.out.println("Different guesses for var " + lhs.getTextContent());
                                        } else {
                                            varNameMap.put(lhs.getTextContent(), guess);
                                        }
                                    } else {
                                        if(lhs.getTextContent().contains("arg")) {
                                            String text = lines.stream().reduce("", String::concat);
                                            p = Pattern.compile("\\(((\\/\\*@ non_null \\*\\/)?\\s*[\\w\\[\\]]*\\s*(\\w*)\\s*)?(\\s*,\\s*(\\/\\*@ non_null \\*\\/)?\\s*[\\w\\[\\]]*\\s*(\\w*))*\\)\\s*[{]");
                                            m = p.matcher(text);
                                            List<String> args = new ArrayList<>();
                                            int linenNum = Integer.parseInt(aLocation.getAttribute("line"));
                                            int numChars = lines.subList(0, linenNum).stream().reduce("", String::concat).length();
                                            while(m.find() && m.start() < numChars) {
                                                args.clear();
                                                for(int k = 0; k < m.groupCount(); ++k) {
                                                    if(k % 3 == 2 && m.group(k + 1) != null && !m.group(k + 1).equals("")) {
                                                        args.add(m.group(k + 1));
                                                        System.out.println("Found arg " + args.get(args.size() - 1));
                                                    }
                                                }
                                            }
                                            int argNum = Integer.parseInt("" + lhs.getTextContent().charAt(lhs.getTextContent().length() - 2));
                                            if(argNum < args.size()) {
                                                guess = args.get(argNum - 1);
                                            } else {
                                                System.out.println("argNum to big.");
                                            }
                                        }
                                        references.add(new Assignment(aLocation.getAttribute("line"), lhs.getTextContent(), value.getTextContent()));
                                    }
                                    System.out.println("in Line " + aLocation.getAttribute("line") + ": " + lhs.getTextContent() + " = " + value.getTextContent());
                                    System.out.println(lines.get(Integer.parseInt(aLocation.getAttribute("line")) - 1));
                                    System.out.println("guess " + guess);
                                }
                            }
                        }
                    }
                }
            }
        } catch (SAXException | IOException | ParserConfigurationException e) {
            System.out.println("Something went wrong parsing xml-file: " + filename);
        }

    }
}
