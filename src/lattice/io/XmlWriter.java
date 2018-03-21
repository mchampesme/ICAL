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
import java.io.Writer;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Vector;

import lattice.gui.OpenFileFrame;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.ScalingFormalAttribute;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.relation.ScalingBinaryRelation;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.CompleteConceptLatticeImp;
import lattice.util.structure.ConceptNode;

/**
 * <p>
 * Titre : Lattice
 * </p>
 * <p>
 * Description : Enregistrement au format XML
 * </p>
 * <p>
 * Copyright : Copyright (c) 2002
 * </p>
 * <p>
 * Soci�t� : Universit� de Montr�al
 * </p>
 * 
 * @author Alexandre Frantz et Pascal Camarda
 * @version 1.0
 */
public class XmlWriter extends AbstractWriter
        implements RelationalContextWriter, LatticeWriter {
    private int typeOfWriting = -1;

    /**
     * Constructeur de la classe
     * 
     * @param fileName
     *            le nom du fichier
     */
    /*
     * public XmlWriter(String fileName) { super(fileName); }
     */

    /**
     * Constructeur de la classe
     * 
     * @param w
     *            le flux en ecriture
     */
    public XmlWriter(Writer w) {
        super(w);
    }

    /**
     * Enregistre une MatrixBinaryRelationBuilder dans le flux
     * 
     * @param lattice
     *            le treillis a enregistrer
     */
    public void writeBinaryRelation(MatrixBinaryRelationBuilder binRel) throws IOException {
        getStream().write("<BIN name=\"" + binRel.getName() + "\" nbObj=\""
                          + binRel.getObjectsNumber() + "\" nbAtt=\""
                          + binRel.getAttributesNumber()
                          + "\" type=\"MatrixBinaryRelationBuilder\">\n");

        getStream().write("<OBJS>\n");
        for (int i = 0; i < binRel.getObjectsNumber(); i++) {
            getStream().write("<OBJ id=\"" + i + "\">");
            getStream().write(binRel.getFormalObject(i).toString());
            getStream().write("</OBJ>\n");
        }
        getStream().write("</OBJS>\n");
        getStream().flush();

        getStream().write("<ATTS>\n");
        for (int i = 0; i < binRel.getAttributesNumber(); i++) {
            getStream().write("<ATT id=\"" + i + "\">");
            getStream().write(binRel.getFormalAttribute(i).toString());
            getStream().write("</ATT>\n");
        }
        getStream().write("</ATTS>\n");
        getStream().flush();

        getStream().write("<RELS>\n");
        for (int i = 0; i < binRel.getObjectsNumber(); i++) {
            for (int j = 0; j < binRel.getAttributesNumber(); j++) {
                if (!binRel.getRelation(i, j).isFalse()) {
                    getStream().write("<REL idObj=\"" + i + "\" idAtt=\"" + j
                                      + "\">");
                    getStream().write("</REL>\n");
                }
            }
            getStream().flush();
        }
        getStream().write("</RELS>\n");
        getStream().write("</BIN>\n");
        getStream().flush();

    }

    public void writeScalingBinaryRelation(ScalingBinaryRelation scBinRel) throws IOException {
        getStream().write("<BIN name=\"" + scBinRel.getName() + "\" nbObj=\""
                          + scBinRel.getObjectsNumber() + "\" nbAtt=\""
                          + scBinRel.getAttributesNumber()
                          + "\" type=\"ScallingBinaryRelation\">\n");

        getStream().write("<ATTS>\n");
        for (int i = 0; i < scBinRel.getAttributesNumber(); i++) {
            getStream()
                    .write("<ATT id=\"" + i + "\" name=\""
                           + ((ScalingFormalAttribute) scBinRel
                                   .getFormalAttribute(i))
                                           .getAttribute().toString()
                           + "\" value=\""
                           + ((ScalingFormalAttribute) scBinRel
                                   .getFormalAttribute(i)).getValue().toString()
                           + "\">");
            getStream().write("</ATT>\n");
        }
        getStream().write("</ATTS>\n");
        getStream().flush();

        getStream().write("<RELS>\n");
        for (int i = 0; i < scBinRel.getObjectsNumber(); i++) {
            for (int j = 0; j < scBinRel.getAttributesNumber(); j++) {
                if (!scBinRel.getRelation(i, j).isFalse()) {
                    getStream().write("<REL idObj=\"" + i + "\" idAtt=\"" + j
                                      + "\">");
                    getStream().write("</REL>\n");
                }
            }
            getStream().flush();
        }
        getStream().write("</RELS>\n");
        getStream().write("</BIN>\n");
        getStream().flush();

    }

    /*
     * (non-Javadoc)
     * @see lattice.io.LatticeWriter#writeConceptLattice(lattice.util.
     * AbstractCompleteConceptLattice)
     */
    public void writeConceptLattice(CompleteConceptLattice lattice) throws BadInputDataException,
                                                                    IOException {

        // Recup�ration des Objets
        int nextIdObj = 0;
        Hashtable lesObjs = new Hashtable();
        for (Iterator it = lattice.getTop().getContent().getExtent()
                .iterator(); it.hasNext();) {
            FormalObject fo = (FormalObject) it.next();
            if (lesObjs.get(fo) == null) {
                lesObjs.put(fo, new Integer(nextIdObj));
                nextIdObj++;
            }
        }

        Double minSup = new Double(lattice.getMinSupp());

        // Recuperation des attributs
        int nextIdAtt = 0;
        Hashtable lesAtts = new Hashtable();
        lattice.getTop().resetDegre();
        Vector Q = new Vector();
        Q.add(lattice.getTop());
        ConceptNode nodeToTest;
        while (Q.size() != 0) {
            nodeToTest = (ConceptNode) Q.remove(0);
            // info pour l'extension lineaire
            for (Iterator it = nodeToTest.getChildren().iterator(); it
                    .hasNext();) {
                ConceptNode P = (ConceptNode) it.next();
                if (P.getDegre() == -1) {
                    P.setDegre(P.getParents().size());
                }
                P.setDegre(P.getDegre() - 1);
                if (P.getDegre() == 0) {
                    Q.add(P);
                }
            }
            for (Iterator it = nodeToTest.getContent().getIntent()
                    .iterator(); it.hasNext();) {
                lesAtts.put(it.next(), new Integer(nextIdAtt));
                nextIdAtt++;
            }
        }

        getStream().write("<LAT Desc=\"" + lattice.getDescription() + "\" ");
        if (lattice instanceof CompleteConceptLatticeImp)
            getStream().write("type=\"ConceptLattice\"");
        getStream().write(">\n");

        getStream().write("<MINSUPP>\n");
        getStream().write(minSup.toString());
        getStream().write("</MINSUPP>\n");

        // Stockage Objets
        getStream().write("<OBJS>\n");
        for (Iterator iter = lesObjs.keySet().iterator(); iter.hasNext();) {
            FormalObject fo = (FormalObject) iter.next();
            getStream().write("<OBJ id=\""
                              + ((Integer) lesObjs.get(fo)).intValue() + "\">");
            getStream().write(fo.toString());
            getStream().write("</OBJ>\n");
        }
        getStream().write("</OBJS>\n");
        getStream().flush();

        // Stockage Attributs
        getStream().write("<ATTS>\n");
        for (Enumeration iter = lesAtts.keys(); iter.hasMoreElements();) {
            FormalAttribute fa = (FormalAttribute) iter.nextElement();
            getStream().write("<ATT id=\""
                              + ((Integer) lesAtts.get(fa)).intValue() + "\">");
            getStream().write(fa.toString());
            getStream().write("</ATT>\n");
        }
        getStream().write("</ATTS>\n");
        getStream().flush();

        getStream().write("<NODS>\n");
        lattice.getTop().resetDegre();
        int nextIdNode = 0;
        Hashtable correspId = new Hashtable();
        Q = new Vector();
        Q.add(lattice.getTop());
        ConceptNode nodeToWrite;
        while (Q.size() != 0) {
            nodeToWrite = (ConceptNode) Q.remove(0);
            getStream().write("<NOD id=\"" + nextIdNode + "\">\n");
            correspId.put(nodeToWrite.getId(), new Integer(nextIdNode));
            nextIdNode++;
            // Stockage Extension
            getStream().write("<EXT>\n");
            for (Iterator it = nodeToWrite.getContent().getExtent()
                    .iterator(); it.hasNext();) {
                getStream().write("<OBJ id=\"" + ((Integer) lesObjs
                        .get((FormalObject) it.next())).intValue() + "\">");
                getStream().write("</OBJ>\n");
            }
            getStream().write("</EXT>\n");

            // Stockage Intension
            getStream().write("<INT>\n");
            for (Iterator it = nodeToWrite.getContent().getIntent()
                    .iterator(); it.hasNext();) {
                getStream().write("<ATT id=\"" + ((Integer) lesAtts
                        .get((FormalAttribute) it.next())).intValue() + "\">");
                getStream().write("</ATT>\n");
            }
            getStream().write("</INT>\n");

            // Stockage Noeud Sup Direct
            getStream().write("<SUP_NOD>\n");
            for (Iterator it = nodeToWrite.getParents().iterator(); it
                    .hasNext();) {
                getStream().write("<PARENT id=\"" + ((Integer) correspId
                        .get(((ConceptNode) it.next()).getId())).intValue()
                                  + "\">");
                getStream().write("</PARENT>\n");
            }
            getStream().write("</SUP_NOD>\n");

            if (nodeToWrite.getContent().getGenerator().size() != 0) {
                // Stockage G�n�rateurs
                getStream().write("<GENS>\n");
                for (Iterator it = nodeToWrite.getContent().getGenerator()
                        .iterator(); it.hasNext();) {
                    getStream().write("<GEN>\n");
                    for (Iterator itG = ((Intent) it.next()).iterator(); itG
                            .hasNext();) {
                        getStream().write("<ATT id=\"" + ((Integer) lesAtts
                                .get((FormalAttribute) itG.next())).intValue()
                                          + "\">");
                        getStream().write("</ATT>\n");
                    }
                    getStream().write("</GEN>\n");
                }
                getStream().write("</GENS>\n");
            }
            if ((lattice.getBottom() != null)
                && (lattice.getBottom().equals(nodeToWrite))) {
                getStream().write("<BOTTOM>\n");
                getStream().write("Je suis bottom");
                getStream().write("</BOTTOM>\n");
            }
            getStream().write("</NOD>\n");

            // info pour l'extension lineaire
            for (Iterator it = nodeToWrite.getChildren().iterator(); it
                    .hasNext();) {
                ConceptNode P = (ConceptNode) it.next();
                if (P.getDegre() == -1) {
                    P.setDegre(P.getParents().size());
                }
                P.setDegre(P.getDegre() - 1);
                if (P.getDegre() == 0) {
                    Q.add(P);
                }
            }
            getStream().flush();
        }
        getStream().write("</NODS>\n");
        getStream().write("</LAT>\n");
        getStream().flush();

    }

    /**
     * Enregistre une MatrixBinaryRelationBuilder dans le flux
     * 
     * @param lattice
     *            le treillis a enregistrer
     */
    public void writeRelationalContext(RelationalContextFamily relCtx) throws IOException {
        getStream().write("<FAM name=\"" + relCtx.getName() + "\">\n");
        for (int i = 0; i < relCtx.size(); i++) {
            if (relCtx.get(i) instanceof ScalingBinaryRelation)
                writeScalingBinaryRelation((ScalingBinaryRelation) relCtx
                        .get(i));
            else if (relCtx.get(i) instanceof MatrixBinaryRelationBuilder)
                writeBinaryRelation((MatrixBinaryRelationBuilder) relCtx
                        .get(i));

            getStream().flush();

            sendJobPercentage((i * 100) / relCtx.size());

        }
        getStream().write("</FAM>\n");
        getStream().flush();

        sendJobPercentage(100);
    }

    public void run() {
        try {
            if (typeOfWriting == OpenFileFrame.BINARY_DATA)
                writeBinaryRelation((MatrixBinaryRelationBuilder) data);
            if (typeOfWriting == OpenFileFrame.FAMILY_DATA)
                writeRelationalContext((RelationalContextFamily) data);
            if (typeOfWriting == OpenFileFrame.LATTICE_DATA)
                writeConceptLattice((CompleteConceptLattice) data);
            getStream().close();
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

    public void setTypeOfWriting(int tw) {
        typeOfWriting = tw;
    }

    public int getTypeOfWriting() {
        return typeOfWriting;
    }

}
