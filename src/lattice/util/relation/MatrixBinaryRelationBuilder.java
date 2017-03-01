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

package lattice.util.relation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Random;

import lattice.alpha.util.BGExtent;
import lattice.alpha.util.BGIntent;
import lattice.alpha.util.Couple;
import lattice.util.concept.AbstractFormalAttributeValue;
import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.DefaultFormalObject;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalAttributeValue;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.exception.BadInputDataException;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.Node;

/**
 * Matrix based implementation of a binary relation builder. 
 * 
 * @author Mr ROUME (for initial BinaryRelation implementation)
 * @author Marc Champesme (refactoring as MatrixBinaryRelationBuilder)
 */
public class MatrixBinaryRelationBuilder implements RelationBuilder {

    public static int NO_SORT = 0;

    public static int AS_EXTENT_SORTED = 1;

    public static int DS_EXTENT_SORTED = 2;

    public static int AS_INTENT_SORTED = 3;

    public static int DS_INTENT_SORTED = 4;

    private String relationName;

    // The corresponding lattice
    private CompleteConceptLattice conceptLattice;

    private List<FormalObject> objectSet;

    private List<FormalAttribute> attributeSet;

    private List<List<AbstractFormalAttributeValue>> hasProperty;

    private int size;

    public static MatrixBinaryRelationBuilder getInstanceFromLattice(
                                                        CompleteConceptLattice lcl) {
        FormalObject fo;
        FormalAttribute fa;
        List<FormalObject> objs = new ArrayList<FormalObject>();
        List<FormalAttribute> atts = new ArrayList<FormalAttribute>();

        // Recuperation des objets
        Iterator<FormalObject> itFobj = lcl.getTop().getContent().getExtent()
                .iterator();
        while (itFobj.hasNext()) {
            objs.add(itFobj.next());
        }

        // Recuperation des attributs
        lcl.getTop().resetDegre();
        List<Node<Concept>> Q = new ArrayList<Node<Concept>>();
        Q.add(lcl.getTop());
        Node<Concept> nodeToTest;
        while (Q.size() != 0) {
            nodeToTest = (Node<Concept>) Q.remove(0);
            // info pour l'extension lineaire
            Iterator<Node<Concept>> itCNode = nodeToTest.getChildren()
                    .iterator();
            while (itCNode.hasNext()) {
                Node<Concept> P = itCNode.next();
                if (P.getDegre() == -1) {
                    P.setDegre(P.getParents().size());
                }
                P.setDegre(P.getDegre() - 1);
                if (P.getDegre() == 0) {
                    Q.add(P);
                }
            }
            Iterator<FormalAttribute> itFatt = nodeToTest.getContent()
                    .getIntent().iterator();
            while (itFatt.hasNext()) {
                atts.add(itFatt.next());
            }
        }

        // creation de la relation binaire
        MatrixBinaryRelationBuilder binRel = new MatrixBinaryRelationBuilder(objs.size(), atts.size());

        // remplissage des objets et attributs
        try {
            for (int i = 0; i < objs.size(); i++) {
                binRel.replaceObject(i, objs.get(i));
            }
            for (int i = 0; i < atts.size(); i++) {
                binRel.replaceAttribute(i, atts.get(i));
            }
        } catch (Exception e) {
            e.printStackTrace();
        }

        // remplissage des relations
        lcl.getTop().resetDegre();
        Q = new ArrayList<Node<Concept>>();
        Q.add(lcl.getTop());
        while (Q.size() != 0) {
            nodeToTest = Q.remove(0);
            // info pour l'extension lineaire
            Iterator<Node<Concept>> itCnode = nodeToTest.getChildren()
                    .iterator();
            while (itCnode.hasNext()) {
                Node<Concept> P = itCnode.next();
                if (P.getDegre() == -1) {
                    P.setDegre(P.getParents().size());
                }
                P.setDegre(P.getDegre() - 1);
                if (P.getDegre() == 0) {
                    Q.add(P);
                }
            }

            Iterator<FormalAttribute> itFatt = nodeToTest.getContent()
                    .getIntent().iterator();
            while (itFatt.hasNext()) {
                fa = itFatt.next();
                Iterator<FormalObject> it2 = nodeToTest.getContent()
                        .getExtent().iterator();
                while (it2.hasNext()) {
                    fo = it2.next();
                    binRel.revertRelation(fo, fa);
                }

            }
        }

        return binRel;
    }

    /**
     * Constructor for MatrixBinaryRelationBuilder.(ref)
     */
    public MatrixBinaryRelationBuilder(int nbObjs, int nbAtts) {
        relationName = DEFAULT_NAME;
        this.objectSet = new ArrayList<FormalObject>(nbObjs);
        this.attributeSet = new ArrayList<FormalAttribute>(nbAtts);
        this.hasProperty = new ArrayList<List<AbstractFormalAttributeValue>>(
                nbObjs);
        for (int i = 0; i < nbObjs; i++) {
            objectSet.add(new DefaultFormalObject("obj_" + i));
        }
        for (int i = 0; i < nbAtts; i++) {
            attributeSet.add(new DefaultFormalAttribute("att_" + i));
        }
        for (int i = 0; i < nbObjs; i++) {
            hasProperty
                    .add(new ArrayList<AbstractFormalAttributeValue>(nbAtts));
        }
        for (int i = 0; i < hasProperty.size(); i++) {
            for (int j = 0; j < attributeSet.size(); j++) {
                hasProperty.get(i).add(FormalAttributeValue.FALSE);
            }
        }
    }

    /**
     * Constructor for MatrixBinaryRelationBuilder.(ref)
     */
    public MatrixBinaryRelationBuilder(String relName, List<FormalObject> objs, List<FormalAttribute> attrs) {
        relationName = relName;
        this.objectSet = objs;
        this.attributeSet = attrs;
        this.hasProperty = new ArrayList<List<AbstractFormalAttributeValue>>(objs.size());
        for (int i = 0; i < objs.size(); i++) {
            hasProperty.add(new ArrayList<AbstractFormalAttributeValue>(attrs.size()));
            for (int j = 0; j < attributeSet.size(); j++) {
                hasProperty.get(i).add(FormalAttributeValue.FALSE);
            }
        }
    }

    /**
     * (ref)
     * 
     * @param relName
     */
    public MatrixBinaryRelationBuilder(String relName) {
        relationName = relName;
        this.objectSet = new ArrayList<FormalObject>();
        this.attributeSet = new ArrayList<FormalAttribute>();
        this.hasProperty = new ArrayList<List<AbstractFormalAttributeValue>>();
    }

    public String getName() {
        return relationName;
    }

    public void setName(String nom) {
        relationName = nom;
    }

    public void setLattice(CompleteConceptLattice cl) {
        conceptLattice = cl;
    }

    public CompleteConceptLattice getLattice() {
        return conceptLattice;
    }

    /*
     * (non-Javadoc) (ref)
     * 
     * @see lattice.util.relation.RelationBuilder#addAttribute()
     */
    public void addAttribute() {
        String aName = "att_";
        int i = attributeSet.size();
        FormalAttribute anAtt = new DefaultFormalAttribute(aName + i);
        while (attributeSet.contains(anAtt)) {
            i++;
            anAtt = new DefaultFormalAttribute(aName + i);
        }
        attributeSet.add(anAtt);
        for (i = 0; i < hasProperty.size(); i++) {
            hasProperty.get(i).add(FormalAttributeValue.FALSE);
        }
    }

    public void addAttribute(FormalAttribute fa) {
        if (!attributeSet.contains(fa)) {
            addAttribute();
            attributeSet.set(attributeSet.size() - 1, fa);
        }
    }

    public void addObject() {
        String oName = "obj_";
        int i = objectSet.size();
        FormalObject anObj = new DefaultFormalObject(oName + i);
        while (objectSet.contains(anObj)) {
            i++;
            anObj = new DefaultFormalObject(oName + i);
        }
        objectSet.add(anObj);
        hasProperty
                .add(new ArrayList<AbstractFormalAttributeValue>(
                                                                 getAttributesNumber()));

        for (int j = 0; j < attributeSet.size(); j++) {
            hasProperty.get(hasProperty.size() - 1)
                    .add(FormalAttributeValue.FALSE);
        }
    }

    public void addObject(FormalObject fo) {
        if (!objectSet.contains(fo)) {
            addObject();
            objectSet.set(objectSet.size() - 1, fo);
        }
    }

    public MatrixBinaryRelationBuilder clone() {
        MatrixBinaryRelationBuilder binRel = null;
        try {
            binRel = (MatrixBinaryRelationBuilder) super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError(e.toString());
        }
        for (int i = 0; i < objectSet.size(); i++) {
            for (int j = 0; j < attributeSet.size(); j++) {
                binRel.setRelation(i, j, !this.getRelation(i, j).isFalse());
            }
        }
        return binRel;
    }

    public boolean contains(FormalAttribute fa) {
        return attributeSet.contains(fa);
    }

    public boolean contains(FormalObject fo) {
        return objectSet.contains(fo);
    }

    public boolean containsObjectForName(String objectName) {
        for (int i = 0; i < objectSet.size(); i++) {
            FormalObject fo = objectSet.get(i);
            String temp = fo.toString();
            if (objectName.compareTo(temp) == 0)
                return true;
        }
        return false;
    }

    public void emptyRelation() {
        for (int i = 0; i < objectSet.size(); i++) {
            for (int j = 0; j < attributeSet.size(); j++) {
                if (!getRelation(i, j).isFalse())
                    revertRelation(i, j);
            }
        }
    }

    public List<FormalAttribute> getAttributes() {
        return Collections.unmodifiableList(attributeSet);
    }

    public int getAttributesNumber() {
        return attributeSet.size();
    }

    public Extent getExtent(FormalAttribute a) {
        Extent extent = new SetExtent();
        int idxA = attributeSet.indexOf(a);
        for (int j = 0; j < objectSet.size(); j++) {
            AbstractFormalAttributeValue value = getRelation(objectSet
                    .get(j), attributeSet.get(idxA));
            if (value.isTrue())
                extent.add(objectSet.get(j));
        }
        return extent;
    }

    public FormalAttribute getFormalAttribute(int idxA) {
        return attributeSet.get(idxA);
    }

    public FormalAttribute getAttributeForName(String attributeName) {
        for (int i = 0; i < attributeSet.size(); i++) {
            if (attributeSet.get(i).toString().equals(attributeName))
                return attributeSet.get(i);
        }
        return null;
    }

    public FormalAttribute[] getFormalAttributes() {
        FormalAttribute[] lesAtts = new FormalAttribute[attributeSet.size()];
        for (int i = 0; i < attributeSet.size(); i++) {
            lesAtts[i] = attributeSet.get(i);
        }
        return lesAtts;
    }

    public FormalObject getFormalObject(int idxO) {
        return objectSet.get(idxO);
    }

    public FormalObject getObjectForName(String objectName) {
        for (int i = 0; i < objectSet.size(); i++) {
            if (objectSet.get(i).toString().equals(objectName))
                return objectSet.get(i);
        }
        return null;
    }

    public FormalObject[] getFormalObjects() {
        FormalObject[] lesObjs = new FormalObject[objectSet.size()];
        for (int i = 0; i < objectSet.size(); i++) {
            lesObjs[i] = objectSet.get(i);
        }
        return lesObjs;
    }

    public Collection<Concept> getInitialAttributePreConcept(int sortType) {
        List<Concept> sortedSetOfConcept = new ArrayList<Concept>();
        Extent lesObjs = null;
        Intent att = null;
        for (int i = 0; i < attributeSet.size(); i++) {
            att = new BGIntent();
            att.add(attributeSet.get(i));
            lesObjs = new BGExtent();
            for (int j = 0; j < objectSet.size(); j++) {
                AbstractFormalAttributeValue absfav = getRelation(
                                                                  objectSet
                                                                          .get(
                                                                               j),
                                                                  attributeSet
                                                                          .get(
                                                                               i));
                if (!absfav.isFalse())
                    lesObjs.add(objectSet.get(j));
            }
            Concept newConcept = new ConceptImp(lesObjs, att);
            if (sortType == NO_SORT) {
                sortedSetOfConcept.add(newConcept);
            } else {
                boolean trouve = false;
                for (int j = 0; j < sortedSetOfConcept.size() && !trouve; j++) {
                    Concept c = sortedSetOfConcept.get(j);
                    if (sortType == AS_EXTENT_SORTED
                        && c.getExtent().size() > newConcept.getExtent().size()) {
                        sortedSetOfConcept.set(j, newConcept);
                        trouve = true;
                    }
                    if (sortType == DS_EXTENT_SORTED
                        && c.getExtent().size() < newConcept.getExtent().size()) {
                        sortedSetOfConcept.set(j, newConcept);
                        trouve = true;
                    }
                }
                if (!trouve)
                    sortedSetOfConcept.add(newConcept);
            }
        }
        return sortedSetOfConcept;
    }

    public Collection<Concept> getInitialObjectPreConcept(int sortType) {
        List<Concept> sortedSetOfConcept = new ArrayList<Concept>();
        Extent obj = null;
        Intent lesAtts = null;
        for (int i = 0; i < objectSet.size(); i++) {
            obj = new BGExtent();
            obj.add(objectSet.get(i));
            lesAtts = new BGIntent();
            for (int j = 0; j < attributeSet.size(); j++) {
                AbstractFormalAttributeValue absfav = getRelation(
                                                                  objectSet
                                                                          .get(
                                                                               i),
                                                                  attributeSet
                                                                          .get(
                                                                               j));
                if (!absfav.isFalse())
                    lesAtts.add(attributeSet.get(j));
            }
            Concept newConcept = new ConceptImp(obj, lesAtts);
            if (sortType == NO_SORT || sortedSetOfConcept.size() == 0) {
                sortedSetOfConcept.add(newConcept);
            } else {
                for (int j = 0; j < sortedSetOfConcept.size(); j++) {
                    if (sortType == AS_INTENT_SORTED
                        && sortedSetOfConcept.get(j).getIntent().size() > newConcept
                                .getIntent().size()) {
                        sortedSetOfConcept.set(j, newConcept);
                        break;
                    }
                    if (sortType == DS_INTENT_SORTED
                        && sortedSetOfConcept.get(j).getIntent().size() < newConcept
                                .getIntent().size()) {
                        sortedSetOfConcept.set(j, newConcept);
                        break;
                    }
                }
            }
        }
        return sortedSetOfConcept;
    }

    public Intent getIntent(FormalObject o) {
        Intent intent = new BGIntent();
        int idxO = objectSet.indexOf(o);
        for (int j = 0; j < attributeSet.size(); j++) {
            AbstractFormalAttributeValue value = getRelation(objectSet
                    .get(idxO), attributeSet.get(j));
            if (value.isTrue())
                intent.add(attributeSet.get(j));
        }
        return intent;
    }

    /* (non-Javadoc)
     * @see lattice.util.relation.RelationBuilder#getObjects()
     */
    public List<FormalObject> getObjects() {
        return Collections.unmodifiableList(objectSet);
    }

    public int getObjectsNumber() {
        return objectSet.size();
    }

    public boolean contains(FormalObject obj, FormalAttribute att) {
        return getRelation(obj, att).isTrue();
    }

    public AbstractFormalAttributeValue getRelation(FormalObject obj,
                                                    FormalAttribute att) {
        int idxO = objectSet.indexOf(obj);
        int idxA = attributeSet.indexOf(att);
        return hasProperty.get(idxO).get(idxA);
    }

    public FormalAttributeValue getRelation(int idxO, int idxA) {
        return (FormalAttributeValue) hasProperty.get(idxO).get(idxA);
    }

    public int randomBinaryRelation(int density) {
        // (FormalAttributeValue)((Vector)aPourProp.elementAt(idxO)).elementAt(idxA);
        int x = 0;
        int y = 0;
        boolean placementOK = false;

        int numAtt = attributeSet.size();
        int numObj = objectSet.size();

        int nbreCoche = numAtt * numObj * density;
        nbreCoche = (int) nbreCoche / 100;

        // System.out.println("Random context generation ("+nbreCoche+"
        // elements).");
        for (int i = 0; i < nbreCoche; i++) {
            placementOK = false;
            Random generateur = new Random();
            while (placementOK == false) {
                y = generateur.nextInt(attributeSet.size());
                x = generateur.nextInt(objectSet.size());
                AbstractFormalAttributeValue previousValue = hasProperty
                        .get(x).get(y);
                if (previousValue.isFalse()) {
                    hasProperty.get(x).set(y, FormalAttributeValue.TRUE);
                    size++;
                    placementOK = true;
                }
            }
        }
        return nbreCoche;
    }

    public void removeAttribute(FormalAttribute fa) {
        int idxA = attributeSet.indexOf(fa);
        attributeSet.remove(idxA);
        for (int i = 0; i < objectSet.size(); i++) {
            if (hasProperty.get(i).get(idxA).isTrue()) {
                size--;
            }
            hasProperty.get(i).remove(idxA);
        }
    }

    public void removeObject(FormalObject fo) {
        int idxO = objectSet.indexOf(fo);
        objectSet.remove(idxO);
        for (int idxA = 0; idxA < attributeSet.size(); idxA++) {
            if (hasProperty.get(idxO).get(idxA).isTrue()) {
                size--;
            }
        }
        hasProperty.remove(idxO);
    }

    public void replaceAttribute(FormalAttribute prevName,
                                 FormalAttribute newName)
                                                         throws BadInputDataException {
        if (prevName.equals(newName))
            return;

        int idx1 = attributeSet.indexOf(prevName);
        if (idx1 == -1) {
            throw new BadInputDataException("The name to replace is missing");
        }
        if (attributeSet.contains(newName)) {
            throw new BadInputDataException(
                                            "The Given name is already existing in the relation");
        }
        attributeSet.set(idx1, newName);
    }

    public void replaceAttribute(int idxA, FormalAttribute newName)
                                                                   throws BadInputDataException {

        if (attributeSet.contains(newName)) {
            throw new BadInputDataException(
                                            "The Given name is already existing in the relation");
        }
        attributeSet.set(idxA, newName);
    }

    public void replaceObject(FormalObject prevName, FormalObject newName)
                                                                          throws BadInputDataException {
        if (prevName.equals(newName))
            return;

        int idx1 = objectSet.indexOf(prevName);
        int idx2 = objectSet.indexOf(newName);
        if (idx1 == -1) {
            throw new BadInputDataException("The name to replace is missing");
        }
        if (idx2 > -1 && idx2 != idx1) {
            throw new BadInputDataException(
                                            "The Given name is already existing in the relation");
        }
        objectSet.set(idx1, newName);
    }

    public void replaceObject(int idxO, FormalObject newName)
                                                             throws BadInputDataException {

        if (idxO < 0 || idxO >= objectSet.size()) {
            throw new BadInputDataException("The indice parameter is not valid");
        }
        int idx2 = objectSet.indexOf(newName);
        if (idx2 > -1 && idx2 != idxO) {
            throw new BadInputDataException(
                                            "The Given name is already existing in the relation");
        }
        objectSet.set(idxO, newName);
    }

    public void revertRelation(FormalObject obj, FormalAttribute att) {
        try {
            if (getRelation(obj, att).isFalse()) {
                setRelation(obj, att, FormalAttributeValue.TRUE);
                size++;
            } else {
                setRelation(obj, att, FormalAttributeValue.FALSE);
                size--;
            }
        } catch (Exception e) {
            System.out.println(e.getMessage() + "\n");
        }
    }

    public void revertRelation(int idxO, int idxA) {
        try {
            if (getRelation(idxO, idxA).isFalse()) {
                setRelation(idxO, idxA, true);
                size++;
            } else {
                setRelation(idxO, idxA, false);
                size--;
            }
        } catch (Exception e) {
            System.out.println(e.getMessage() + "\n");
        }
    }

    public void setRelation(FormalObject Obj, FormalAttribute Att,
                            AbstractFormalAttributeValue rel)
                                                             throws BadInputDataException {
        setRelation(Obj, Att, (FormalAttributeValue) rel);
    }

    public void setRelation(FormalObject Obj, FormalAttribute Att,
                            FormalAttributeValue rel)
                                                     throws BadInputDataException {
        if (!rel.toString().equals("0") && !rel.toString().equals("X")) {
            throw new BadInputDataException(
                                            "Bad input format for Setting a Relation");
        } else {
            int idxO = objectSet.indexOf(Obj);
            int idxA = attributeSet.indexOf(Att);
            if (rel.isTrue() && hasProperty.get(idxO).get(idxA).isFalse()) {
                size++;
            }
            if (rel.isFalse() && hasProperty.get(idxO).get(idxA).isTrue()) {
                size--;
            }
            hasProperty.get(idxO).set(idxA, rel);
        }
    }

    public void setRelation(int idxO, int idxA, boolean val) {
        if (idxO < objectSet.size() && idxA < attributeSet.size()
            && val) {
            if (hasProperty.get(idxO).get(idxA).isFalse()) {
                size++;
            }
            hasProperty.get(idxO).set(idxA, FormalAttributeValue.TRUE);
        }
        if (idxO < objectSet.size() && idxA < attributeSet.size()
            && !val) {
            if (hasProperty.get(idxO).get(idxA).isTrue()) {
                size--;
            }
            hasProperty.get(idxO).set(idxA, FormalAttributeValue.FALSE);
        }
    }

    public String toString() {
        return getName();
    }

    public int hashCode() {
        return toString().hashCode();
    }

    public Iterator<FormalAttribute> attributeIterator() {
        return attributeSet.iterator();
    }

    public Iterator<Couple<FormalObject, FormalAttribute>> iterator() {
        return new MatrixBinaryRelationIterator(objectSet, attributeSet, hasProperty
                .iterator());
    }

    public Iterator<FormalObject> objectIterator() {
        return objectSet.iterator();
    }

    public int size() {
        return size;
    }

    /**
     * @return the objectSet
     */
    protected List<FormalObject> getObjectSet() {
        return objectSet;
    }

    /**
     * @return the attributeSet
     */
    protected List<FormalAttribute> getAttributeSet() {
        return attributeSet;
    }

}
