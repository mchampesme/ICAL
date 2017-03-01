/*
 * **********************************************************************
 * Copyright (C) 2004 The Galicia Team Modifications to the initial code base
 * are copyright of their respective authors, or their employers as appropriate.
 * Authorship of the modifications may be determined from the ChangeLog placed
 * at the end of this file. This program is free software; you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of the
 * License, or (at your option) any later version. This program is distributed
 * in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even
 * the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details. You should have
 * received a copy of the GNU Lesser General Public License along with this
 * program; if not, write to the Free Software Foundation, Inc., 59 Temple
 * Place, Suite 330, Boston, MA 02111-1307 USA; or visit the following url:
 * http://www.gnu.org/copyleft/lesser.html
 * **********************************************************************
 */

package lattice.io;

import java.io.IOException;
import java.io.Reader;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import lattice.gui.OpenFileFrame;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.DefaultFormalObject;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalAttributeValue;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.InterObjectBinaryRelationAttribute;
import lattice.util.concept.ScalingFormalAttribute;
import lattice.util.concept.ScalingFormalObject;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.relation.ScalingBinaryRelation;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.CompleteConceptLatticeImp;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
import lattice.util.structure.LatticeGraph;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.w3c.dom.Text;
import org.xml.sax.InputSource;

/**
 * <p>
 * Titre : Lattice
 * </p>
 * <p>
 * Description : Lecture du format XML - treillis construit
 * </p>
 * <p>
 * Copyright : Copyright (c) 2002
 * </p>
 * <p>
 * Société : Université de Montréal
 * </p>
 * 
 * @author Alexandre Frantz et Pascal Camarda
 * @version 1.0
 */
public class XmlReader extends AbstractReader implements
        RelationalContextReader, LatticeReader {

    private int typeOfReading = -1;

    private Element currentTag = null;

    /**
     * Constructeur de la classe
     * 
     * @param fileName
     *            le nom du fichier
     */
    /*
     * public XmlReader(String fileName) { super(fileName); }
     */

    /**
     * Constructeur de la classe
     * 
     * @param r
     *            le flux
     */
    public XmlReader(Reader r) {
        super(r);
    }

    /**
     * Lit le fichier
     * 
     * @return Vector - les elements du treillis
     */
    public Vector read() {
        return null;
    }

    /**
     * Futur Implementation !
     * 
     * @return
     */
    public MatrixBinaryRelationBuilder readBinaryRelation() throws BadInputDataException,
                                              IOException {
        FormalObject fo = null;
        FormalAttribute fa = null;
        if (currentTag != null && currentTag.getTagName().equals("BIN")
            && Integer.parseInt(currentTag.getAttribute("nbObj")) > 0
            && Integer.parseInt(currentTag.getAttribute("nbAtt")) > 0
            && currentTag.getAttribute("type").equals("MatrixBinaryRelationBuilder")) {
            MatrixBinaryRelationBuilder binRel = new MatrixBinaryRelationBuilder(Integer
                    .parseInt(currentTag.getAttribute("nbObj")), Integer
                    .parseInt(currentTag.getAttribute("nbAtt")));
            binRel.setName(currentTag.getAttribute("name"));
            NodeList nl = ((Element) currentTag.getElementsByTagName("OBJS")
                    .item(0)).getElementsByTagName("OBJ");
            for (int i = 0; i < nl.getLength(); i++) {
                Element obj = (Element) nl.item(i);
                fo = new DefaultFormalObject(((Text) obj.getChildNodes()
                        .item(0)).getNodeValue());
                binRel.replaceObject(Integer.parseInt(obj.getAttribute("id")),
                                     fo);
            }
            nl = ((Element) currentTag.getElementsByTagName("ATTS").item(0))
                    .getElementsByTagName("ATT");
            for (int i = 0; i < nl.getLength(); i++) {
                Element att = (Element) nl.item(i);
                fa = new DefaultFormalAttribute(((Text) att.getChildNodes()
                        .item(0)).getNodeValue());
                binRel.replaceAttribute(Integer
                        .parseInt(att.getAttribute("id")), fa);
            }
            nl = ((Element) currentTag.getElementsByTagName("RELS").item(0))
                    .getElementsByTagName("REL");
            for (int i = 0; i < nl.getLength(); i++) {
                Element rel = (Element) nl.item(i);
                binRel.setRelation(Integer.parseInt(rel.getAttribute("idObj")),
                                   Integer.parseInt(rel.getAttribute("idAtt")),
                                   true);
            }
            return binRel;
        } else {
            if (currentTag == null)
                System.out.println("null");
            throw new BadInputDataException(
                                            "Reading XML MatrixBinaryRelationBuilder wrong format!");
        }
    }

    /**
     * Futur Implementation !
     * 
     * @return
     */
    public InterObjectBinaryRelation readInterObjectBinaryRelation()
                                                                    throws BadInputDataException,
                                                                    IOException {
        FormalObject fo = null;
        FormalAttribute fa = null;
        if (currentTag != null
            && currentTag.getTagName().equals("BIN")
            && Integer.parseInt(currentTag.getAttribute("nbObj")) > 0
            && Integer.parseInt(currentTag.getAttribute("nbAtt")) > 0
            && currentTag.getAttribute("type")
                    .equals("InterObjectBinaryRelation")) {
            InterObjectBinaryRelation binRel = new InterObjectBinaryRelation(
                                                                             Integer
                                                                                     .parseInt(currentTag
                                                                                             .getAttribute("nbObj")),
                                                                             Integer
                                                                                     .parseInt(currentTag
                                                                                             .getAttribute("nbAtt")));
            binRel.setName(currentTag.getAttribute("name"));

            // Added by Amine June 23, 2004, 16:56
            NodeList nl = ((Element) currentTag.getElementsByTagName("LINKS")
                    .item(0)).getElementsByTagName("LINK");
            Element ctx = (Element) nl.item(0);
            String objectsCtx = new String(((Text) ctx.getChildNodes().item(0))
                    .getNodeValue());
            ctx = (Element) nl.item(1);
            String attributesCtx = new String(((Text) ctx.getChildNodes()
                    .item(0)).getNodeValue());
            binRel.setObjectsContextName(objectsCtx);
            binRel.setAttributesContextName(attributesCtx);
            // end added by Amine

            nl = ((Element) currentTag.getElementsByTagName("OBJS").item(0))
                    .getElementsByTagName("OBJ");
            for (int i = 0; i < nl.getLength(); i++) {
                Element obj = (Element) nl.item(i);
                fo = new DefaultFormalObject(((Text) obj.getChildNodes()
                        .item(0)).getNodeValue());
                binRel.replaceObject(Integer.parseInt(obj.getAttribute("id")),
                                     fo);
            }
            nl = ((Element) currentTag.getElementsByTagName("ATTS").item(0))
                    .getElementsByTagName("ATT");
            for (int i = 0; i < nl.getLength(); i++) {
                Element att = (Element) nl.item(i);
                fa = new InterObjectBinaryRelationAttribute(
                                                            new DefaultFormalObject(
                                                                                    ((Text) att
                                                                                            .getChildNodes()
                                                                                            .item(
                                                                                                  0))
                                                                                            .getNodeValue()));
                binRel.replaceAttribute(Integer
                        .parseInt(att.getAttribute("id")), fa);
            }
            nl = ((Element) currentTag.getElementsByTagName("RELS").item(0))
                    .getElementsByTagName("REL");
            for (int i = 0; i < nl.getLength(); i++) {
                Element rel = (Element) nl.item(i);
                binRel.setRelation(Integer.parseInt(rel.getAttribute("idObj")),
                                   Integer.parseInt(rel.getAttribute("idAtt")),
                                   true);
            }
            return binRel;
        } else {
            throw new BadInputDataException(
                                            "Reading XML MatrixBinaryRelationBuilder wrong format!");
        }
    }

    /**
     * Futur Implementation !
     * 
     * @return
     */
    public ScalingBinaryRelation readScalingBinaryRelation()
                                                            throws BadInputDataException,
                                                            IOException {
        FormalAttribute fa = null;
        FormalAttributeValue fav = null;
        if (currentTag != null && currentTag.getTagName().equals("BIN")
            && Integer.parseInt(currentTag.getAttribute("nbObj")) > 0
            && Integer.parseInt(currentTag.getAttribute("nbAtt")) > 0
            && currentTag.getAttribute("type").equals("ScallingBinaryRelation")) {
            MatrixBinaryRelationBuilder binRel = new ScalingBinaryRelation(Integer
                    .parseInt(currentTag.getAttribute("nbObj")), Integer
                    .parseInt(currentTag.getAttribute("nbAtt")));
            binRel.setName(currentTag.getAttribute("name"));
            Hashtable currentAtt = new Hashtable();
            Hashtable currentVal = new Hashtable();
            NodeList nl = ((Element) currentTag.getElementsByTagName("ATTS")
                    .item(0)).getElementsByTagName("ATT");
            for (int i = 0; i < nl.getLength(); i++) {
                Element att = (Element) nl.item(i);
                fa = (FormalAttribute) currentAtt.get(att.getAttribute("name"));
                if (fa == null) {
                    fa = new DefaultFormalAttribute(att.getAttribute("name"));
                    currentAtt.put(att.getAttribute("name"), fa);
                }
                fav = (FormalAttributeValue) currentVal.get(att
                        .getAttribute("value"));
                if (fav == null) {
                    String strAttValue = att.getAttribute("value");
                    if (strAttValue.equals("0")) {
                        fav = FormalAttributeValue.FALSE;
                    } else if (strAttValue.equals("X")) {
                        fav = FormalAttributeValue.TRUE;
                    } else {
                        fav = new FormalAttributeValue(strAttValue);
                    }
                    currentVal.put(att.getAttribute("value"), fav);
                }

                binRel.replaceAttribute(i, new ScalingFormalAttribute(fa, fav));
                binRel.replaceObject(i, new ScalingFormalObject(fa, fav));
            }
            nl = ((Element) currentTag.getElementsByTagName("RELS").item(0))
                    .getElementsByTagName("REL");
            for (int i = 0; i < nl.getLength(); i++) {
                Element rel = (Element) nl.item(i);
                binRel.setRelation(Integer.parseInt(rel.getAttribute("idObj")),
                                   Integer.parseInt(rel.getAttribute("idAtt")),
                                   true);
            }
            return (ScalingBinaryRelation) binRel;
        }
        return null;
    }

    /**
     * Futur Implementation !
     * 
     * @return
     */
    public RelationalContextFamily readRelationalContext()
                                                          throws BadInputDataException,
                                                          IOException {
        if (currentTag != null && currentTag.getTagName().equals("FAM")) {
            RelationalContextFamily relCtx = new RelationalContextFamily(
                                                                         currentTag
                                                                                 .getAttribute("name"));
            for (int i = 0; i < currentTag.getChildNodes().getLength(); i++) {

                if (currentTag.getChildNodes().item(i).getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
                    currentTag = (Element) currentTag.getChildNodes().item(i);

                    if (currentTag.getTagName().equals("BIN")
                        && currentTag.getAttribute("type")
                                .equals("MatrixBinaryRelationBuilder")) {
                        relCtx.add(readBinaryRelation());
                        currentTag = (Element) currentTag.getParentNode();
                    } else if (currentTag.getTagName().equals("BIN")
                               && currentTag.getAttribute("type")
                                       .equals("ScallingBinaryRelation")) {
                        relCtx.add(readScalingBinaryRelation());
                        currentTag = (Element) currentTag.getParentNode();
                    } else if (currentTag.getTagName().equals("BIN")
                               && currentTag.getAttribute("type")
                                       .equals("InterObjectBinaryRelation")) {
                        relCtx.add(readInterObjectBinaryRelation());
                        currentTag = (Element) currentTag.getParentNode();
                    }
                }
            }
            return relCtx;
        } else {
            throw new BadInputDataException(
                                            "Reading XML MatrixBinaryRelationBuilder wrong format!");
        }
    }

    /**
     * Futur Implementation !
     * 
     * @return
     */
    public CompleteConceptLattice readConceptLattice()
                                                      throws BadInputDataException,
                                                      IOException {
        if (currentTag != null && currentTag.getTagName().equals("LAT")) {
            CompleteConceptLattice lcl = null;
            if (currentTag.getAttribute("type").equals("ConceptLattice"))
                lcl = new CompleteConceptLatticeImp();
            if (currentTag.getAttribute("type").equals("LatticeGraph"))
                lcl = new LatticeGraph();

            Map<String, FormalObject> idObj = new Hashtable<String, FormalObject>();
            Map<String, FormalAttribute> idAtt = new Hashtable<String, FormalAttribute>();
            Map<String, ConceptNode> idNode = new Hashtable<String, ConceptNode>();

            NodeList nl = ((Element) currentTag.getElementsByTagName("OBJS")
                    .item(0)).getElementsByTagName("OBJ");
            for (int i = 0; i < nl.getLength(); i++) {
                Element obj = (Element) nl.item(i);
                idObj.put(obj.getAttribute("id"),
                          new DefaultFormalObject(((Text) obj.getChildNodes()
                                  .item(0)).getNodeValue()));
            }
            nl = ((Element) currentTag.getElementsByTagName("ATTS").item(0))
                    .getElementsByTagName("ATT");
            for (int i = 0; i < nl.getLength(); i++) {
                Element att = (Element) nl.item(i);
                idAtt.put(att.getAttribute("id"),
                          new DefaultFormalAttribute(((Text) att
                                  .getChildNodes().item(0)).getNodeValue()));
            }
            nl = ((Element) currentTag.getElementsByTagName("NODS").item(0))
                    .getElementsByTagName("NOD");
            boolean firstNode = true;
            for (int i = 0; i < nl.getLength(); i++) {
                Element nod = (Element) nl.item(i);
                Extent extent = new SetExtent();
                Intent intent = new SetIntent();
                NodeList nl2 = ((Element) nod.getElementsByTagName("EXT")
                        .item(0)).getElementsByTagName("OBJ");
                for (int j = 0; j < nl2.getLength(); j++) {
                    Element obj = (Element) nl2.item(j);
                    extent.add(idObj.get(obj.getAttribute("id")));
                }
                nl2 = ((Element) nod.getElementsByTagName("INT").item(0))
                        .getElementsByTagName("ATT");
                for (int j = 0; j < nl2.getLength(); j++) {
                    Element att = (Element) nl2.item(j);
                    intent.add(idAtt.get(att.getAttribute("id")));
                }
                ConceptNode newNode = new ConceptNodeImp(new ConceptImp(extent,
                                                                        intent));
                if (firstNode) {
                    lcl.setTop(newNode);
                    firstNode = false;
                    if (lcl instanceof CompleteConceptLatticeImp) {
                        ((CompleteConceptLatticeImp) lcl).incNbOfNodes();
                    }
                    if (nod.getElementsByTagName("GENS").item(0) != null) {
                        List<Intent> gen = new Vector<Intent>();
                        nl2 = ((Element) nod.getElementsByTagName("GENS")
                                .item(0)).getElementsByTagName("GEN");
                        for (int j = 0; j < nl2.getLength(); j++) {
                            Intent generator = new SetIntent();
                            NodeList nl3 = ((Element) ((Element) nod
                                    .getElementsByTagName("GENS").item(0))
                                    .getElementsByTagName("GEN").item(j))
                                    .getElementsByTagName("ATT");
                            for (int k = 0; k < nl3.getLength(); k++) {
                                Element att = (Element) nl3.item(k);
                                generator
                                        .add(idAtt.get(att.getAttribute("id")));
                            }
                            gen.add(generator);
                        }
                        newNode.getContent().setGenerator(gen);
                    }
                    if (nod.getElementsByTagName("BOTTOM").item(0) != null)
                        lcl.setBottom(newNode);
                } else {
                    nl2 = ((Element) nod.getElementsByTagName("SUP_NOD")
                            .item(0)).getElementsByTagName("PARENT");
                    for (int j = 0; j < nl2.getLength(); j++) {
                        Element parent = (Element) nl2.item(j);
                        ConceptNode supNode = (ConceptNode) idNode.get(parent
                                .getAttribute("id"));
                        newNode.addParent(supNode);
                        supNode.addChild(newNode);
                    }
                    if (nod.getElementsByTagName("GENS").item(0) != null) {
                        Vector gen = new Vector();
                        nl2 = ((Element) nod.getElementsByTagName("GENS")
                                .item(0)).getElementsByTagName("GEN");
                        for (int j = 0; j < nl2.getLength(); j++) {
                            Intent generator = new SetIntent();
                            NodeList nl3 = ((Element) ((Element) nod
                                    .getElementsByTagName("GENS").item(0))
                                    .getElementsByTagName("GEN").item(j))
                                    .getElementsByTagName("ATT");
                            for (int k = 0; k < nl3.getLength(); k++) {
                                Element att = (Element) nl3.item(k);
                                generator
                                        .add(idAtt.get(att.getAttribute("id")));
                            }
                            gen.add(generator);
                        }
                        newNode.getContent().setGenerator(gen);
                    }
                    if (nod.getElementsByTagName("BOTTOM").item(0) != null) {
                        lcl.setBottom(newNode);
                    }

                    else {
                        Extent bottomExtent = new SetExtent();
                        Intent bottomIntent = new SetIntent();
                        Iterator iter = idAtt.values().iterator();
                        while (iter.hasNext()) {
                            FormalAttribute fa = (FormalAttribute) iter.next();
                            bottomIntent.add(fa);
                        }
                        ConceptImp bottomFictif = new ConceptImp(bottomExtent,
                                                                 bottomIntent);
                        ConceptNode tempBottom = new ConceptNodeImp(
                                                                    bottomFictif);
                        lcl.setBottom(tempBottom);
                    }

                    if (lcl instanceof LatticeGraph) {
                        ((LatticeGraph) lcl).add(newNode);
                    }
                    if (lcl instanceof CompleteConceptLatticeImp) {
                        ((CompleteConceptLatticeImp) lcl).incNbOfNodes();
                    }
                }
                idNode.put(nod.getAttribute("id"), newNode);
            }

            return lcl;
        } else {
            throw new BadInputDataException(
                                            "Reading XML MatrixBinaryRelationBuilder wrong format!");
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Runnable#run()
     */
    public void run() {

        try {
            // -- créer un document
            DocumentBuilder docBuilder = DocumentBuilderFactory.newInstance()
                    .newDocumentBuilder();
            InputSource is = new InputSource(getStream());

            // -- analyse du fichier
            Document doc = docBuilder.parse(is);

            // -- parcours du fichier
            currentTag = doc.getDocumentElement();

            if (typeOfReading == OpenFileFrame.BINARY_DATA)
                data = readBinaryRelation();
            if (typeOfReading == OpenFileFrame.FAMILY_DATA)
                data = readRelationalContext();
            if (typeOfReading == OpenFileFrame.LATTICE_DATA)
                data = readConceptLattice();
        } catch (Exception e) {
            e.printStackTrace();
            if (jobObserv != null) {
                jobObserv.sendMessage(e.getMessage());
                jobObserv.jobEnd(false);
            }
            return;
        }
        if (jobObserv != null)
            jobObserv.jobEnd(true);
    }

    public void setTypeOfReading(int tr) {
        typeOfReading = tr;
    }

    public int getTypeOfReading() {
        return typeOfReading;
    }
}
