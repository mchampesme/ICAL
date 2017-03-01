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
/*
 *  Copyright LIPN
 *  contributor(s) : Marc Champesme (2006) marc.champesme@lipn.univ-paris13.fr
 *  
 *  This software is a computer program whose purpose is the Incremental construction of Alpha lattices.
 *  
 *  This software is governed by the CeCILL license under French law and
 *  abiding by the rules of distribution of free software.  You can  use, 
 *  modify and/ or redistribute the software under the terms of the CeCILL
 *  license as circulated by CEA, CNRS and INRIA at the following URL
 *  "http://www.cecill.info". 
 *  
 *  As a counterpart to the access to the source code and  rights to copy,
 *  modify and redistribute granted by the license, users are provided only
 *  with a limited warranty  and the software's author,  the holder of the
 *  economic rights,  and the successive licensors  have only  limited
 *  liability. 
 *  
 *  In this respect, the user's attention is drawn to the risks associated
 *  with loading,  using,  modifying and/or developing or reproducing the
 *  software by the user in light of its specific status of free software,
 *  that may mean  that it is complicated to manipulate,  and  that  also
 *  therefore means  that it is reserved for developers  and  experienced
 *  professionals having in-depth computer knowledge. Users are therefore
 *  encouraged to load and test the software's suitability as regards their
 *  requirements in conditions enabling the security of their systems and/or 
 *  data to be ensured and,  more generally, to use and operate it in the 
 *  same conditions as regards security. 
 *  
 *  The fact that you are presently reading this means that you have had
 *  knowledge of the CeCILL license and that you accept its terms.
 */

package lattice.alpha.iceberg.algorithm;

import java.util.Date;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import lattice.algorithm.LatticeAlgorithm;
import lattice.alpha.util.BGConcept;
import lattice.alpha.util.BGConceptNode;
import lattice.alpha.util.BitSetExtent;
import lattice.alpha.util.BitSetIntent;
import lattice.util.concept.Concept;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.Node;
import orderedset.ArrayHashSet;

/**
 * 
 * @author zuojin (for original Galicia implementation of class
 *         lattice.iceberg.algorithm.BordatIceberg)
 * @author Marc Champesme
 */

public class BordatLatticeBuilder extends LatticeAlgorithm {
    private Map<FormalObject, Intent> objToIntentMap;

    private Concept bottomConcept;

    private ArrayHashSet<FormalObject> extentDomain;

    private BitSetExtent classObjectSet;

    private ArrayHashSet<FormalAttribute> intentDomain;

    public BordatLatticeBuilder(MatrixBinaryRelationBuilder relation, double minSupp,
                                Map<FormalObject, Intent> objToIntentMap,
                                BitSetExtent classObjectSet,
                                Set<FormalAttribute> intentDomain) {

        super(relation);
        setminSupp(minSupp);

        // begin Amine
        BGConceptNode.resetNodeId();
        // end Amine

        System.out.println("New BordatLatticeBuilder start at " + new Date());

        Concept topConcept = null;

        this.objToIntentMap = objToIntentMap;
        this.classObjectSet = classObjectSet;
        this.extentDomain = (ArrayHashSet<FormalObject>) classObjectSet
                .domain();
        if (intentDomain instanceof ArrayHashSet) {
            this.intentDomain = (ArrayHashSet<FormalAttribute>) intentDomain;
        } else {
            this.intentDomain = new ArrayHashSet<FormalAttribute>(intentDomain);
        }

        topConcept = makeTopConcept();

        bottomConcept = makeBottomConcept();

        CompleteConceptLattice resultLattice = getLattice();
        resultLattice.setTop(new BGConceptNode(topConcept));
        resultLattice.incNbOfNodes();
        resultLattice.setBottom(new BGConceptNode(bottomConcept));
        resultLattice.incNbOfNodes();
        resultLattice
                .initialiseIntentLevelIndex(relation.getAttributesNumber() + 1);
        resultLattice.add(resultLattice.getBottom());

    }

    public void doAlgorithm() {

        // jobObserv.sendMessage("Bordat Algorithm is in progress!\n");
        Node<Concept> top = getLattice().getTop();

        if (!bottomConcept.equals(top.getContent())) {
            // if bottom and top are the same concept,
            // there is nothing to do
            doBordat(top);
        }

        // jobObserv.jobEnd(true);

    }

    public String getDescription() {
        return "Bordat Lattice Builder";
    }

    /**
     * Construct and return a new instance which represents the top concept of
     * the lattice. The top concept is defined here as the concept whose extent
     * is the set of all objects of the given relation.
     * 
     * @return the concept whose extent is the set of all objects
     */
    public Concept makeTopConcept() {
        Concept top = null;
        BitSetIntent topIntent = null;
        Extent topExtent = new BitSetExtent(extentDomain, classObjectSet);

        Iterator<FormalObject> objIter = classObjectSet.iterator();
        FormalObject currentObject = null;

        if (objIter.hasNext()) {
            currentObject = objIter.next();
            topIntent = (BitSetIntent) objToIntentMap.get(currentObject);
            topIntent = (BitSetIntent) topIntent.clone();
        } else {
            topIntent = new BitSetIntent(intentDomain);
        }

        while (objIter.hasNext()) {
            currentObject = objIter.next();
            BitSetIntent intent = (BitSetIntent) objToIntentMap
                    .get(currentObject);
            topIntent.fastRetainAll(intent);
        }

        top = new BGConcept(topExtent, topIntent);

        return top;
    }

    /**
     * Construct and return a new instance which represents the bottom concept
     * of the lattice. The bottom concept is defined here as the concept whose
     * intent is the set of all attributes of the given relation.
     * 
     * @return the concept whose intent is the set of all attributes
     */
    public Concept makeBottomConcept() {
        Concept bottom = null;
        Extent bottomExtent = new BitSetExtent(extentDomain);
        Intent bottomIntent = new BitSetIntent(intentDomain, intentDomain);
        List<FormalObject> objList = this.getBinaryRelation().getObjects();

        for (FormalObject currentObject : getBinaryRelation().getObjects()) {
            if (objToIntentMap.get(currentObject).equals(bottomIntent)) {
                // object whose intent is the complete set of
                // attributes are in the extension of the bottom Concept
                bottomExtent.add(currentObject);
            }
        }
        double bottomCover = (double) bottomExtent.size()
                             / (double) objList.size();
        if (!bottomExtent.isEmpty() && bottomCover < getminSupp()) {
            bottomExtent.clear();
        }

        bottom = new BGConcept(bottomExtent, bottomIntent);

        return bottom;

    }

    public Concept getTop() {
        return getLattice().getTop().getContent();
    }

    public void doBordat(Node<Concept> top) {
        long nodeProcessed = 0;
        Concept concept = top.getContent();
        LinkedList<Node<Concept>> candidate = new LinkedList<Node<Concept>>();
        Map<Concept, Node<Concept>> conceptToNodeMap = new Hashtable<Concept, Node<Concept>>();
        Node<Concept> bottomNode = getLattice().getBottom();

        conceptToNodeMap.put(concept, top);
        conceptToNodeMap.put(bottomNode.getContent(), bottomNode);

        candidate.addLast(top);

        Date dateStart = new Date();
        System.out.println("BordatLatticeBuilder:start at "
                           + dateStart.toString());

        do {
            nodeProcessed++;
            if (nodeProcessed % 1000 == 0) {
                Date date = new Date();
                System.out.println("Process the " + nodeProcessed
                                   + "th node at " + date);
            }

            top = candidate.getFirst();

            concept = top.getContent();

            List<Concept> lowerCoverFirst = findLowerCover(concept);
            // System.out.println("lowerConcept#" + nodeProcessed + ":" +
            // lowerCoverFirst);
            double brObjectNumber = (double) getBinaryRelation()
                    .getObjectsNumber();
            int childNumber = 0;

            for (Concept lowerConcept : lowerCoverFirst) {
                Node<Concept> childNode;
                double lowerConceptCover = lowerConcept.getExtent().size()
                                           / brObjectNumber;

                // System.out.println("BordatLatticeBuilder(minSupp=" +
                // getminSupp() + "): concept#"
                // + lowerConcept + "has lowerConceptCover=" +
                // lowerConceptCover);
                if (lowerConceptCover >= getminSupp()
                    && lowerConceptCover != 0.0) {
                    childNumber++;
                    childNode = conceptToNodeMap.get(lowerConcept);

                    if (childNode == null) {
                        childNode = new BGConceptNode(lowerConcept);
                        conceptToNodeMap.put(lowerConcept, childNode);
                        candidate.addLast(childNode);
                        getLattice().incNbOfNodes();
                    }
                    childNode.linkToUpperCovers(top);
                }
            }
            if (childNumber == 0) {
                bottomNode.linkToUpperCovers(top);
            }
            getLattice().add(top);
            candidate.removeFirst();
        } while (!candidate.isEmpty());

        Date dateEnd = new Date();
        System.out.println("BordatLatticeBuilder:The resulting lattice has "
                           + getLattice().size()
                           + " nodes, processing terminated at " + dateEnd);
        long time = dateEnd.getTime() - dateStart.getTime();
        long timeSec = (long) (time / 1000);
        long timeMin = (long) (timeSec / 60);
        System.out.println("BordatLatticeBuilder: Total processing time "
                           + time + "ms or " + timeMin + "mn "
                           + (timeSec - timeMin * 60) + "s");
        // System.out.println("BordatLatticeBuilder: bottomConcept of lattice is
        // " + getLattice().getBottomConceptNode().getConcept());
        // System.out.println("BordatLatticeBuilder: bottomConcept has " +
        // getLattice().getBottomConceptNode().getParents().size() + "
        // parents.");
    }

    /**
     * @param concept
     * @return a list of concept
     */
    /*
     * @ @ requires concept != null; @ ensures \result != null; @ ensures
     * (\forall int i; i >= 0 && i < \result.size(); @ \result.get(i) instanceof
     * Concept); @
     */
    public List<Concept> findLowerCover(Concept concept) {
        BitSetExtent refExtent = (BitSetExtent) concept.getExtent();
        BitSetIntent refIntent = (BitSetIntent) concept.getIntent();
        List<Concept> lowerCover = new LinkedList<Concept>();
        BitSetIntent refIntentCopy = (BitSetIntent) refIntent.clone();
        FormalObject firstObj;

        Iterator<FormalObject> objIter = refExtent.iterator();
        firstObj = findFirstObj(refIntentCopy, objIter);
        BitSetExtent objExtent = new BitSetExtent(extentDomain);
        while (firstObj != null) {
            // @ assume refIntentCopy.containsAll(refIntent);
            BitSetIntent objIntent = (BitSetIntent) objToIntentMap
                    .get(firstObj);
            // @ assume !refIntentCopy.containsAll(objIntent);
            // @ assume objIntent.containsAll(refIntent);
            objExtent.clear();
            objExtent.fastAdd(firstObj);

            while (objIter.hasNext()) {
                FormalObject nextObj = (FormalObject) objIter.next();
                BitSetIntent nextObjIntent = (BitSetIntent) objToIntentMap
                        .get(nextObj);
                BitSetIntent newIntent = (BitSetIntent) nextObjIntent
                        .intersection(objIntent);
                if (!(refIntentCopy.containsAll(newIntent))) {
                    objExtent.fastAdd(nextObj);
                    objIntent = newIntent;
                }
            }

            if (objIntent.intersection(refIntentCopy).equals(refIntent)) {
                // System.out.println("Found lower cover:" + objExtent + "@" +
                // objIntent);
                lowerCover.add(new BGConcept((Extent) objExtent.clone(),
                                             (Intent) objIntent.clone()));
            }

            refIntentCopy.fastAddAll(objIntent);
            objIter = refExtent.iterator();
            firstObj = findFirstObj(refIntentCopy, objIter);
        }

        // Here we need add the bottomConcept Node of the
        // lattice!!!!!!!!!!!!!!!!!
        int nbrAttrsOfBottom = bottomConcept.getIntent().size();
        if (lowerCover.isEmpty() && (refIntent.size() != nbrAttrsOfBottom)) {
            System.out.println("lowerCover.isEmpty(): adding bottom");
            lowerCover.add(this.bottomConcept);
        } else {
            if (lowerCover.isEmpty()) {
                System.out
                        .println("lowerCover.isEmpty() and current intent is:");
            }
        }

        return lowerCover;
    }

    /**
     * Search the first object of the specified iterator whose intent is not
     * included in the specified intent and return this object if it exists.
     * 
     * @param intent
     *            the intent to which compare the intents of the objects
     * @param objIter
     *            An iterator over FormalObject
     * @return the first object of the specified iterator whose intent is not
     *         included in the specified intent if it exists ; null otherwise.
     */
    /*
     * @ @ requires intent != null && objIter != null; @ requires
     * objIter.elementType <: \type(FormalObject); @ assignable
     * objIter.objectState; @ ensures
     * !intent.containsAll(getIntentForObject(\result)); @
     */
    protected FormalObject findFirstObj(Intent intent, Iterator<FormalObject> objIter) {
        FormalObject firstObj = null;
        // System.out.println("findFirstObj(" + intent + ")?");

        while (objIter.hasNext() && firstObj == null) {
            FormalObject obj = objIter.next();
            Intent objIntent = objToIntentMap.get(obj);
            // System.out.println(obj + "->" + objIntent);

            if (intent.containsAll(objIntent)) {
                firstObj = null;
            } else {
                firstObj = obj;
            }
        }
        // System.out.println("->" + firstObj);
        return firstObj;
    }

    /**
     * Returns the intent of the specified FormalObject, if this object belongs
     * to the relation.
     * 
     * @param fo
     *            the object whose associated intent is to be returned.
     * @return the intent associated with this object or null if this object is
     *         not known by this relation.
     */
    /*
     * @ @ requires fo != null; @ {| @ requires (* fo is int this relation *); @
     * ensures \result != null; @ also @ requires (* fo is not in this relation
     * *); @ ensures \result == null; @ |} @ pure @
     */
    public Intent getIntentForObject(FormalObject fo) {
        return objToIntentMap.get(fo);
    }

    /**
     * @return Returns the bottomConcept.
     */
    public Concept getBottom() {
        return bottomConcept;
    }
}
