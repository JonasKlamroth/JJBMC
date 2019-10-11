import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class XmlParser {

    public static JBMCOutput parse(String xmlFile, String sourceFile) {
        File xmlF = new File(xmlFile);
        File sourceF = new File(sourceFile);
        DocumentBuilder dBuilder = null;
        try {
            dBuilder = DocumentBuilderFactory.newInstance().newDocumentBuilder();
        } catch (ParserConfigurationException e) {
            e.printStackTrace();
        }
        Document doc = null;
        try {
            doc = dBuilder.parse(xmlF);
        } catch (SAXException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }
        return parse(doc, sourceF);
    }

    public static JBMCOutput parse(String xmlContent, File sourceFile) {
        DocumentBuilder dBuilder = null;
        JBMCOutput res = new JBMCOutput();
        try {
            dBuilder = DocumentBuilderFactory.newInstance().newDocumentBuilder();
        } catch (ParserConfigurationException e) {
            e.printStackTrace();
            return null;
        }
        Document doc = null;
        try {
            InputSource is = new InputSource(new StringReader(xmlContent));
            doc = dBuilder.parse(is);
        } catch (SAXException e) {
            e.printStackTrace();
            return null;
        } catch (IOException e) {
            e.printStackTrace();
            return null;
        }
        doc.getDocumentElement().normalize();
        return parse(doc, sourceFile);
    }

    public static JBMCOutput parse(Document xmlDoc, File sourceFile) {
        List<JBMCOutput.Assignment> references = new ArrayList<>();
        Map<String, String> varNameMap = new HashMap<>();
        File f1 = sourceFile;
        List<String> lines = new ArrayList<>();
        try {
            lines = Files.readAllLines(f1.toPath());
        } catch (IOException e) {
            System.out.println("Error reading file: " + f1.getAbsolutePath());
            return null;
        }
        JBMCOutput res = new JBMCOutput();
        Document doc = xmlDoc;
        doc.getDocumentElement().normalize();
        NodeList statusList = doc.getElementsByTagName("cprover-status");
        assert statusList.getLength() == 1;
        res.proverStatus = statusList.item(0).getTextContent();
        NodeList messageList = doc.getElementsByTagName("messaage");
        for(int i = 0; i < messageList.getLength(); ++i) {
            res.messages.add(messageList.item(i).getTextContent());
        }
        NodeList propertyNodeList = doc.getElementsByTagName("result");
        boolean someFail = false;
        for(int i = 0; i < propertyNodeList.getLength(); ++i) {
            Node propertyNode = propertyNodeList.item(i);
            if (propertyNode.getNodeType() == Node.ELEMENT_NODE) {
                references = null;
                Element propertyElemnt = (Element) propertyNode;
                int lineNumber = -1;
                if(propertyElemnt.getAttribute("status").equals("FAILURE")) {
                    references = new ArrayList<>();
                    someFail = true;
                    Element failure = (Element)propertyElemnt.getElementsByTagName("failure").item(0);
                    Element location = (Element) failure.getElementsByTagName("location").item(0);
                    lineNumber = Integer.parseInt(location.getAttribute("line"));
                    NodeList assignmentList = ((Element) propertyNode).getElementsByTagName("assignment");
                    for(int j = 0; j < assignmentList.getLength(); ++j) {
                        Element assignment = (Element)assignmentList.item(j);
                        if(assignment.getElementsByTagName("location").getLength() > 0) {
                            Element aLocation = (Element) assignment.getElementsByTagName("location").item(0);
                            Element lhs = (Element) assignment.getElementsByTagName("full_lhs").item(0);
                            Element value = (Element) assignment.getElementsByTagName("value").item(0);
                            String l = lines.get(Integer.parseInt(aLocation.getAttribute("line")) - 1);
                            if(assignment.getAttribute("hidden").equals("false") && lhs.getTextContent().contains("this") || lhs.getTextContent().contains("anonlocal") || lhs.getTextContent().contains("arg")) {
                                Pattern p = Pattern.compile("(\\w*) ?= ?.*?;");
                                Matcher m = p.matcher(l);
                                String guess = null;
                                if(m.find()) {
                                    guess = m.group(1);
                                    references.add(new JBMCOutput.Assignment(aLocation.getAttribute("line"), lhs.getTextContent(), guess, value.getTextContent()));
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
                                    references.add(new JBMCOutput.Assignment(aLocation.getAttribute("line"), lhs.getTextContent(), guess, value.getTextContent()));
                                }
                              //  System.out.println("in Line " + aLocation.getAttribute("line") + ": " + lhs.getTextContent() + " = " + value.getTextContent());
                              //  System.out.println(lines.get(Integer.parseInt(aLocation.getAttribute("line")) - 1));
                              //  System.out.println("guess " + guess);
                            }
                        }
                    }
                }
                if(lineNumber < 0) {
                    res.addProperty(propertyElemnt.getAttribute("property"), references, lineNumber, null);
                } else {
                    res.addProperty(propertyElemnt.getAttribute("property"), references, lineNumber, lines.get(lineNumber - 1));
                }
            }
        }
        if (!someFail) System.out.println("No fail.");

        return res;
    }
}
