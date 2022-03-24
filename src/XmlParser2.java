import com.sun.tools.javac.util.Pair;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jmlspecs.annotation.In;
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
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class XmlParser2 {
    private static final Logger log = LogManager.getLogger(XmlParser2.class);
    private static final String jbmcBanner = "\n" +
            "* *             JBMC 5.22.0 (cbmc-5.22.0) 64-bit            * *\n" +
            "* *                 Copyright (C) 2001-2018                 * *\n" +
            "* *              Daniel Kroening, Edmund Clarke             * *\n" +
            "* * Carnegie Mellon University, Computer Science Department * *\n" +
            "* *                  kroening@kroening.com                  * *";

    public static JBMCOutput parse(File xmlFile, boolean printTrace, TraceInformation ti) {
        DocumentBuilder dBuilder;
        Document doc = null;
        try {
            dBuilder = DocumentBuilderFactory.newInstance().newDocumentBuilder();
            doc = dBuilder.parse(xmlFile);
        } catch (ParserConfigurationException | SAXException | IOException e) {
            e.printStackTrace();
        }
        return parse(doc, printTrace, ti);
    }

    public static JBMCOutput parse(String xmlContent, boolean printTrace, TraceInformation ti) {
        DocumentBuilder dBuilder;
        try {
            dBuilder = DocumentBuilderFactory.newInstance().newDocumentBuilder();
        } catch (ParserConfigurationException e) {
            e.printStackTrace();
            return null;
        }
        Document doc;
        try {
            InputSource is = new InputSource(new StringReader(xmlContent));
            doc = dBuilder.parse(is);
        } catch (SAXException e) {
            if(xmlContent.startsWith(jbmcBanner)) {
                log.error("Error calling jbmc. Possibly provided faulty jbmc-arguments?");
                return null;
            }
            e.printStackTrace();
            return null;
        } catch (IOException e) {
            e.printStackTrace();
            return null;
        }
        doc.getDocumentElement().normalize();
        return parse(doc, printTrace, ti);
    }

    public static JBMCOutput parse(Document xmlDoc, boolean printTrace, TraceInformation ti) {
        JBMCOutput res = new JBMCOutput();
        try {
            JBMCOutput.Trace trace = null;
            xmlDoc.getDocumentElement().normalize();
            NodeList messageList = xmlDoc.getElementsByTagName("message");
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
            NodeList statusList = xmlDoc.getElementsByTagName("cprover-status");
            assert statusList.getLength() == 1;
            res.proverStatus = statusList.item(0).getTextContent();
            if(!printTrace) {
                return res;
            }
            NodeList propertyNodeList = xmlDoc.getElementsByTagName("result");
            String reason;
            for (int i = 0; i < propertyNodeList.getLength(); ++i) {
                reason = null;
                Node propertyNode = propertyNodeList.item(i);
                if (propertyNode.getNodeType() == Node.ELEMENT_NODE) {
                    Element propertyElemnt = (Element) propertyNode;
                    int lineNumber = -1;
                    if (propertyElemnt.getAttribute("status").equals("FAILURE")) {

                        Element failure = (Element) propertyElemnt.getElementsByTagName("failure").item(0);
                        reason = failure.getAttribute("reason");
                        Element location = (Element) failure.getElementsByTagName("location").item(0);
                        if(location == null) {
                            if(propertyElemnt.getAttribute("property").contains("unwind")) {
                                res.addProperty("Unwinding assertion", new JBMCOutput.Trace(new ArrayList<>()), -1, "Try to increase the unwinding parameter.", null);
                                return res;
                            } else {
                                throw new Exception("location was null.");
                            }
                        } else {
                            lineNumber = Integer.parseInt(location.getAttribute("line"));
                        }
                        Pair<Integer, Integer> relevantRange = ti.getRelevantRange(lineNumber);
                        NodeList assignmentList = ((Element) propertyNode).getElementsByTagName("assignment");
                        List<JBMCOutput.Assignment> assignments = new ArrayList<>();
                        List<JBMCOutput.Assignment> lineAssignments = new ArrayList<>();
                        int lastLine = -1;
                        for (int j = 0; j < assignmentList.getLength(); ++j) {
                            Element assignment = (Element) assignmentList.item(j);
                            if (assignment.getElementsByTagName("location").getLength() > 0) {
                                Element aLocation = (Element) assignment.getElementsByTagName("location").item(0);
                                Element lhs = (Element) assignment.getElementsByTagName("full_lhs").item(0);
                                Element value = (Element) assignment.getElementsByTagName("full_lhs_value").item(0);
                                int line = Integer.parseInt(aLocation.getAttribute("line"));
                                int origLine = ti.getOriginalLine(line);
                                if(line > lastLine && line < relevantRange.snd && line >= relevantRange.fst) {
                                    ti.provideGuesses(lineAssignments);
                                    lineAssignments = new ArrayList<>();
                                    lastLine = line;
                                }
                                String parameterName = null;
                                if(assignment.getAttribute("assignment_type").equals("actual_parameter")) {
                                    parameterName = assignment.getAttribute("display_name");
                                }
                                JBMCOutput.Assignment assignment1 = new JBMCOutput.Assignment(line, lhs.getTextContent(), value.getTextContent(), null, parameterName);
                                lineAssignments.add(assignment1);
                                assignments.add(assignment1);

                                //if(guess != null) {
                                    //log.info("in line " + ti.getOriginalLine(line) + ": " + guess + " = " + value.getTextContent() + " (" + lhs.getTextContent() + ")");
                                //}
                            }
                        }
                        trace = extractTrace(assignments);
                        if(reason.contains("assertion")) {
                            trace.relevantVars = ti.getAssertVarsForLine(lineNumber);
                        }
                    }
                    if (lineNumber < 0) {
                        res.addProperty(propertyElemnt.getAttribute("property"), null, lineNumber, null, null);
                    } else {
                        if(reason.contains("assertion")) {
                            res.addProperty(propertyElemnt.getAttribute("property"), trace, ti.getOriginalLine(lineNumber), reason, ti.getAssertForLine(lineNumber));
                        } else {
                            res.addProperty(propertyElemnt.getAttribute("property"), trace, ti.getOriginalLine(lineNumber), reason, null);
                        }
                    }
                }
            }
        } catch (Exception e) {
            log.info("Error parsing xml file.");
            TransformerFactory tf = TransformerFactory.newInstance();
            Transformer transformer;
            try {
                transformer = tf.newTransformer();
                transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
                transformer.setOutputProperty(OutputKeys.INDENT, "no");
                StringWriter writer = new StringWriter();
                transformer.transform(new DOMSource(xmlDoc), new StreamResult(writer));
                String output = writer.toString();
                log.debug(output);
            } catch (TransformerException ex) {
                ex.printStackTrace();
            }
            e.printStackTrace();
        }

        return res;
    }

    public static JBMCOutput.Trace extractTrace(List<JBMCOutput.Assignment> assignments) {
        //for(JBMCOutput.Assignment a : assignments) {
            //log.info("assignment in line " + a.lineNumber + ": " + a.guess + " (" + a.jbmcVarname + ") = " + a.value);
        //}
        return new JBMCOutput.Trace(assignments);
    }

    private static String getOriginalName(String[] exprs, Map<String, String> exprMap) {
        StringBuilder res = new StringBuilder();
        for(String s : exprs) {
            res.append(getOriginalName(s, exprMap));
        }
        return res.toString();
    }
    private static String getOriginalName(String expr, Map<String, String> exprMap) {
        while(exprMap.containsKey(expr)) {
            expr = exprMap.get(expr);
            String[] exprs = expr.split("((?<=([.\\[\\]])|(?=([.\\[\\]]))))");
            if(exprs.length > 1) {
                expr = getOriginalName(exprs, exprMap);
            }
        }
        return expr;
    }
}
