import com.sun.tools.javac.util.Pair;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.nio.file.Files;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class XmlParser {
    private static Logger log = LogManager.getLogger(XmlParser.class);

    public static JBMCOutput parse(String xmlFile, String sourceFile, Map<String, List<String>> paramMap) {
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
        return parse(doc, sourceF, paramMap);
    }

    public static JBMCOutput parse(String xmlContent, File sourceFile, Map<String, List<String>> paramMap) {
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
        return parse(doc, sourceFile, paramMap);
    }

    public static JBMCOutput parse(Document xmlDoc, File sourceFile, Map<String, List<String>> paramMap) {
        JBMCOutput res = new JBMCOutput();
        try {
            JBMCOutput.Trace references = null;
            List<Pair<String, String>> assignments = new ArrayList<>();
            List<Integer> lineNumbers = new ArrayList<>();
            List<String> sourceLines = new ArrayList<>();
            File f1 = sourceFile;
            List<String> lines = new ArrayList<>();
            try {
                lines = Files.readAllLines(f1.toPath());
            } catch (IOException e) {
                log.error("Error reading file: " + f1.getAbsolutePath());
                return null;
            }
            String joined = String.join("\n", lines);
            Document doc = xmlDoc;
            doc.getDocumentElement().normalize();
            NodeList messageList = doc.getElementsByTagName("message");
            for (int i = 0; i < messageList.getLength(); ++i) {
                if(((Element)(messageList.item(i))).getAttribute("type").equals("ERROR")) {
                    res.errors.add(messageList.item(i).getTextContent());
                } else {
                    res.messages.add(messageList.item(i).getTextContent());
                }
            }
            if(res.errors.size() > 0) {
                res.proverStatus = "ERROR";
                return res;
            }
            NodeList statusList = doc.getElementsByTagName("cprover-status");
            assert statusList.getLength() == 1;
            res.proverStatus = statusList.item(0).getTextContent();
            NodeList propertyNodeList = doc.getElementsByTagName("result");
            String reason = null;
            for (int i = 0; i < propertyNodeList.getLength(); ++i) {
                reason = null;
                Node propertyNode = propertyNodeList.item(i);
                if (propertyNode.getNodeType() == Node.ELEMENT_NODE) {
                    references = null;
                    Element propertyElemnt = (Element) propertyNode;
                    int lineNumber = -1;
                    if (propertyElemnt.getAttribute("status").equals("FAILURE")) {

                        Element failure = (Element) propertyElemnt.getElementsByTagName("failure").item(0);
                        reason = failure.getAttribute("reason");
                        Element location = (Element) failure.getElementsByTagName("location").item(0);
                        if(location == null) {
                            if(propertyElemnt.getAttribute("property").contains("unwind")) {
                                res.addProperty("Unwinding assertion", new JBMCOutput.Trace(new ArrayList<>(), new HashSet<>()), -1, null, "Try to increase the unwinding parameter.");
                                return res;
                            } else {
                                throw new Exception("location was null.");
                            }
                        } else {
                            lineNumber = Integer.parseInt(location.getAttribute("line"));
                        }
                        NodeList assignmentList = ((Element) propertyNode).getElementsByTagName("assignment");
                        for (int j = 0; j < assignmentList.getLength(); ++j) {
                            Element assignment = (Element) assignmentList.item(j);
                            if (assignment.getElementsByTagName("location").getLength() > 0) {
                                Element aLocation = (Element) assignment.getElementsByTagName("location").item(0);
                                Element lhs = (Element) assignment.getElementsByTagName("full_lhs").item(0);
                                Element value = (Element) assignment.getElementsByTagName("full_lhs_value").item(0);
                                int line = Integer.parseInt(aLocation.getAttribute("line")) - 1;
                                if(line < 0 || line >= lines.size()) {
                                    //something is fishy
                                    continue;
                                }
                                String l = lines.get(line);
                                assignments.add(new Pair<String, String>(lhs.getTextContent(), value.getTextContent()));
                                lineNumbers.add(line);
                                sourceLines.add(l);

                            }
                        }
                        references = extractTrace(assignments, sourceLines, lineNumbers, paramMap, propertyElemnt.getAttribute("property"));
                    }
                    if (lineNumber < 0) {
                        res.addProperty(propertyElemnt.getAttribute("property"), references, lineNumber, null, null);
                    } else {
                        res.addProperty(propertyElemnt.getAttribute("property"), references, lineNumber, lines.get(lineNumber - 1), reason);
                    }
                }
            }
        } catch (Exception e) {
            log.info("Error parsing xml file.");
            TransformerFactory tf = TransformerFactory.newInstance();
            Transformer transformer = null;
            try {
                transformer = tf.newTransformer();
            } catch (TransformerConfigurationException ex) {
                ex.printStackTrace();
            }
            transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
            transformer.setOutputProperty(OutputKeys.INDENT, "no");
            StringWriter writer = new StringWriter();
            try {
                transformer.transform(new DOMSource(xmlDoc), new StreamResult(writer));
            } catch (TransformerException ex) {
                ex.printStackTrace();
            }
            String output = writer.toString();
            log.debug(output);
            e.printStackTrace();
        }

        return res;
    }

    public static JBMCOutput.Trace extractTrace(List<Pair<String, String>> assignments, List<String> sourceLines, List<Integer> lineNumbers, Map<String, List<String>> paramMap, String propertyName) {
        for(int i = assignments.size() - 1; i >= 0; --i) {
            if(!(assignments.get(i).fst.startsWith("tmp_object_factory") || assignments.get(i).fst.startsWith("dynamic") || assignments.get(i).fst.startsWith("arg") || assignments.get(i).fst.startsWith("anonlocal") || assignments.get(i).fst.startsWith("this"))) {
                assignments.remove(i);
                sourceLines.remove(i);
                lineNumbers.remove(i);
            }
            if(assignments.get(i).fst.endsWith("class_identifier")) {
                assignments.set(i, new Pair<>(assignments.get(i).fst.substring(0, assignments.get(i).fst.indexOf(".")), assignments.get(i).snd));
            }
            if(assignments.get(i).fst.contains(".data")) {
                assignments.set(i, new Pair<>(assignments.get(i).fst.replace(".data", ""), assignments.get(i).snd));
            }
        }
        Map<String, String> nameMap = new HashMap<>();
        nameMap.put("tmp_object_factory", "this");
        for(int i = 0; i < assignments.size(); ++i) {
            String var = assignments.get(i).fst;
            String val = assignments.get(i).snd;
            if(val.startsWith("(void *)&dynamic_object")) {
                val = val.substring(9, val.indexOf("."));
            }
            if(val.startsWith("&dynamic_object")) {
                val = val.substring(1);
            }
            try {
                Integer.parseInt(val);
                continue;
            } catch (NumberFormatException e) {
            }
            if(!val.equals("null")) {
                nameMap.put(val, var);
            }
        }

        List<JBMCOutput.Assignment> trace = new ArrayList<>();
        Set<JBMCOutput.Trace.Guess> guesses = new HashSet<>();
        for(int i = 0; i < assignments.size(); ++i) {
            String var = assignments.get(i).fst;
            String[] split = var.split("((?<=(\\.|\\[|\\])|(?=(\\.|\\[|\\]))))");
            var = getOriginalName(split, nameMap);
            String guess = guessVarName(var, sourceLines.get(i), paramMap, propertyName);
            if(guess != null) {
                guesses.add(new JBMCOutput.Trace.Guess(var, guess, lineNumbers.get(i)));
            }
            trace.add(new JBMCOutput.Assignment(lineNumbers.get(i) + 1, var, assignments.get(i).snd, sourceLines.get(i)));
        }
        return new JBMCOutput.Trace(trace, guesses);
    }

    private static String guessVarName(String var, String sourceLine, Map<String, List<String>> paramMap, String propertyName) {
        String ident_regex = "[A-Za-z0-9_]+";
        if(var.startsWith("anonlocal")) {
            String postfix = "";
            if(var.contains(".")) {
                postfix = var.substring(var.indexOf(".") + 1);
                ident_regex = "(" + ident_regex + ")\\." + postfix;
                postfix = "." + postfix;
            } else if (var.contains("[")){
                postfix = var.substring(var.indexOf("[") + 1);
                ident_regex = "(" + ident_regex + ")\\[.*?\\]\\S*?";
                postfix = "[" + postfix;
            } else {
                ident_regex = "(" + ident_regex + ")";
            }
            List<String> allMatches = new ArrayList<String>();
            Matcher m = Pattern.compile(".*?" + ident_regex + " ?(\\+|\\*|-|~|/)?= ?.*?")
                    .matcher(sourceLine);
            while (m.find()) {
                allMatches.add(m.group(1));
            }
            m = Pattern.compile(".*?" + ident_regex + "((\\+\\+)|(\\-\\-)).*")
                    .matcher(sourceLine);
            while (m.find()) {
                allMatches.add(m.group(1));
            }
            m = Pattern.compile(".*?((\\-\\-)|(\\+\\+))" + ident_regex  + ".*")
                    .matcher(sourceLine);
            while (m.find()) {
                allMatches.add(m.group(4));
            }
            if(allMatches.size() == 1) {
                return allMatches.get(0) + postfix;
            } else {
                List<String> distinct = allMatches.stream().distinct().collect(Collectors.toList());
                if(distinct.size() == 1) {
                    return distinct.get(0) + postfix;
                }
            }
        }
        Matcher m = Pattern.compile("arg(\\d+)\\w(.*)")
                .matcher(var);
        if(m.find()) {
            try {
                int idx = Integer.parseInt(m.group(1)) ;
                String postfix = m.group(2);
                m = Pattern.compile("java::(.*?):")
                        .matcher(propertyName);
                if(m.find()) {
                    String functionName = m.group(1);
                    if(paramMap.containsKey(functionName)) {
                        List<String> args = paramMap.get(functionName);
                        idx -= 1;
                        if(idx >= 0 && idx < args.size()) {
                            return args.get(idx) + postfix;
                            //return null;
                        }
                    }
                    functionName = "$static_" + functionName;
                    if(paramMap.containsKey(functionName)) {
                        List<String> args = paramMap.get(functionName);
                        if(idx >= 0 && idx < args.size()) {
                            return args.get(idx) + postfix;
                        }
                    }
                }
            } catch (NumberFormatException e) {
                //meh
            }
        }
        return null;
    }


    private static String getOriginalName(String[] exprs, Map<String, String> exprMap) {
        String res = "";
        for(String s : exprs) {
            res += getOriginalName(s, exprMap);
        }
        return res;
    }
    private static String getOriginalName(String expr, Map<String, String> exprMap) {
        while(exprMap.containsKey(expr)) {
            expr = exprMap.get(expr);
            String[] exprs = expr.split("((?<=(\\.|\\[|\\])|(?=(\\.|\\[|\\]))))");
            if(exprs.length > 1) {
                expr = getOriginalName(exprs, exprMap);
            }
        }
        return expr;
    }
}
