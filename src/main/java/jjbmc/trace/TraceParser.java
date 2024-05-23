package jjbmc.trace;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import jjbmc.Assignment;
import jjbmc.ErrorLogger;
import jjbmc.JBMCOutput;
import com.github.javaparser.utils.Pair;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import static jjbmc.ErrorLogger.*;

public class TraceParser {
    private static final ErrorLogger log = new ErrorLogger();

    private static final String jbmcBanner = """

            * *             JBMC 5.22.0 (cbmc-5.22.0) 64-bit            * *
            * *                 Copyright (C) 2001-2018                 * *
            * *              Daniel Kroening, Edmund Clarke             * *
            * * Carnegie Mellon University, Computer Science Department * *
            * *                  kroening@kroening.com                  * *""";

    public static JBMCOutput parse(File xmlFile, boolean printTrace) throws ParserConfigurationException, IOException, SAXException {
        DocumentBuilder builder;
        builder = DocumentBuilderFactory.newInstance().newDocumentBuilder();
        Document doc = builder.parse(xmlFile);
        return parse(doc, printTrace);
    }

    public static JBMCOutput parse(String xmlContent, boolean printTrace) throws ParserConfigurationException, SAXException, IOException {
        DocumentBuilder builder = DocumentBuilderFactory.newInstance().newDocumentBuilder();
        try {
            InputSource is = new InputSource(new StringReader(xmlContent));
            Document doc = builder.parse(is);
            doc.getDocumentElement().normalize();
            return parse(doc, printTrace);
        } catch (SAXException | IOException e) {
            if (xmlContent.startsWith(jbmcBanner)) {
                error("Error calling jbmc. Possibly provided faulty jbmc-arguments?");
            }
            throw e;
        }
    }

    public static JBMCOutput parse(Document xmlDoc, boolean printTrace) {
        JBMCOutput res = new JBMCOutput();
        try {
            Trace trace = null;
            xmlDoc.getDocumentElement().normalize();
            NodeList messageList = xmlDoc.getElementsByTagName("message");
            for (int i = 0; i < messageList.getLength(); ++i) {
                if (((Element) (messageList.item(i))).getAttribute("type").equals("ERROR")) {
                    res.getErrors().add(messageList.item(i).getTextContent());
                } else {
                    res.getMessages().add(messageList.item(i).getTextContent());
                }
            }
            if (!res.getErrors().isEmpty()) {
                res.setProverStatus("ERROR");
                return res;
            }
            NodeList statusList = xmlDoc.getElementsByTagName("cprover-status");
            assert statusList.getLength() == 1;
            res.setProverStatus(statusList.item(0).getTextContent());
            if (!printTrace) {
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

                        Element failure = (Element) propertyElemnt
                                .getElementsByTagName("failure")
                                .item(0);
                        reason = failure.getAttribute("reason");
                        Element location = (Element) failure
                                .getElementsByTagName("location")
                                .item(0);
                        if (location == null) {
                            if (propertyElemnt.getAttribute("property").contains("unwind")) {
                                res.addProperty("Unwinding assertion",
                                        new Trace(new ArrayList<>()),
                                        -1,
                                        "Try to increase the unwinding parameter.", null);
                                return res;
                            } else {
                                throw new Exception("location was null.");
                            }
                        } else {
                            lineNumber = Integer.parseInt(location.getAttribute("line"));
                        }
                        Pair<Integer, Integer> relevantRange = TraceInformation.getRelevantRange(lineNumber);
                        NodeList assignmentList = ((Element) propertyNode).getElementsByTagName("assignment");
                        List<Assignment> assignments = new ArrayList<>();
                        List<Assignment> lineAssignments = new ArrayList<>();
                        int lastLine = -1;
                        for (int j = 0; j < assignmentList.getLength(); ++j) {
                            Element assignment = (Element) assignmentList.item(j);
                            if (assignment.getElementsByTagName("location").getLength() > 0) {
                                Element location1 = (Element) assignment.getElementsByTagName("location").item(0);
                                Element lhs = (Element) assignment.getElementsByTagName("full_lhs").item(0);
                                Element value = (Element) assignment.getElementsByTagName("full_lhs_value").item(0);
                                int line = Integer.parseInt(location1.getAttribute("line"));
                                //int origLine = TraceInformation.getOriginalLine(line);
                                if (line > lastLine && line < relevantRange.b && line >= relevantRange.a) {
                                    //trace.provideGuesses(lineAssignments);
                                    lineAssignments = new ArrayList<>();
                                    lastLine = line;
                                }
                                String parameterName = null;
                                if (assignment.getAttribute("assignment_type").equals("actual_parameter")) {
                                    parameterName = assignment.getAttribute("display_name");
                                }
                                Assignment assignment1 = new Assignment(line,
                                        lhs.getTextContent(), value.getTextContent(), null, parameterName);
                                lineAssignments.add(assignment1);
                                assignments.add(assignment1);
                            }
                        }
                        trace = extractTrace(assignments);
                        if (reason.contains("assertion")) {
                            trace.setRelevantVars(TraceInformation.getAssertVarsForLine(lineNumber));
                        }
                    }
                    if (lineNumber < 0) {
                        res.addProperty(propertyElemnt.getAttribute("property"), null, lineNumber, null, null);
                    } else {
                        if (reason.contains("assertion")) {
                            res.addProperty(propertyElemnt.getAttribute("property"),
                                    trace,
                                    TraceInformation.getOriginalLine(lineNumber),
                                    reason,
                                    TraceInformation.getAssertForLine(lineNumber));
                        } else {
                            res.addProperty(propertyElemnt.getAttribute("property"),
                                    trace,
                                    TraceInformation.getOriginalLine(lineNumber),
                                    reason,
                                    null);
                        }
                    }
                }
            }
        } catch (Exception e) {
            info("Error parsing xml file.");
            TransformerFactory tf = TransformerFactory.newInstance();
            Transformer transformer;
            try {
                transformer = tf.newTransformer();
                transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
                transformer.setOutputProperty(OutputKeys.INDENT, "no");
                StringWriter writer = new StringWriter();
                transformer.transform(new DOMSource(xmlDoc), new StreamResult(writer));
                String output = writer.toString();
                debug(output);
            } catch (TransformerException ex) {
                ex.printStackTrace();
            }
            e.printStackTrace();
        }

        return res;
    }

    public static Trace extractTrace(List<Assignment> assignments) {
        return new Trace(assignments);
    }

    private static String getOriginalName(String[] exprs, Map<String, String> exprMap) {
        StringBuilder res = new StringBuilder();
        for (String s : exprs) {
            res.append(getOriginalName(s, exprMap));
        }
        return res.toString();
    }

    private static String getOriginalName(String expr, Map<String, String> exprMap) {
        while (exprMap.containsKey(expr)) {
            expr = exprMap.get(expr);
            String[] exprs = expr.split("((?<=([.\\[\\]])|(?=([.\\[\\]]))))");
            if (exprs.length > 1) {
                expr = getOriginalName(exprs, exprMap);
            }
        }
        return expr;
    }
}
