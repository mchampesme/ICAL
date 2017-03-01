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
package lattice.alpha.util;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.structure.CompleteConceptLattice;
import orderedset.ArrayHashSet;

/**
 * @author Marc Champesme
 */
public class BitSetBinaryRelation implements Relation {

    private String relName;

    private int size;

    private CompleteConceptLattice lattice;

    private ArrayHashSet<FormalObject> objectSet;

    private ArrayHashSet<FormalObject> objectDomain;

    private ArrayHashSet<FormalAttribute> attributeSet;

    private ArrayHashSet<FormalAttribute> attributeDomain;

    private Map<FormalObject, BitSetIntent> objToIntent;

    private Map<FormalAttribute, BitSetExtent> attrToExtent;

    public BitSetBinaryRelation(Relation relation) {
        relName = relation.getName();
        objectSet = new ArrayHashSet<FormalObject>(relation.getObjects());
        objectDomain = objectSet;
        attributeSet = new ArrayHashSet<FormalAttribute>(relation
                .getAttributes());
        attributeDomain = attributeSet;
        objToIntent = new HashMap<FormalObject, BitSetIntent>(relation
                .getObjectsNumber() * 4 / 3);
        attrToExtent = new HashMap<FormalAttribute, BitSetExtent>(relation
                .getAttributesNumber() * 4 / 3);
        for (Couple<FormalObject, FormalAttribute> couple : relation) {
            FormalObject fo = couple.first();
            FormalAttribute fa = couple.second();
            BitSetIntent intent = objToIntent.get(fo);
            BitSetExtent extent = attrToExtent.get(fa);
            if (intent == null) {
                intent = new BitSetIntent(attributeDomain);
                objToIntent.put(fo, intent);
            }
            intent.add(fa);
            if (extent == null) {
                extent = new BitSetExtent(objectDomain);
                attrToExtent.put(fa, extent);
            }
            extent.add(fo);
            size++;
        }
    }

    public BitSetBinaryRelation(AlphaContext context, FormalAttribute classAttr) {
        relName = classAttr.getName();
        objectSet = new ArrayHashSet<FormalObject>(context
                .getObjectsForClass(classAttr));
        objectDomain = new ArrayHashSet<FormalObject>(context.getObjects());
        attributeSet = new ArrayHashSet<FormalAttribute>(context
                .getAttributes());
        attributeDomain = attributeSet;
        objToIntent = new HashMap<FormalObject, BitSetIntent>(
                                                              objectSet.size() * 4 / 3);
        attrToExtent = new HashMap<FormalAttribute, BitSetExtent>(context
                .getAttributesNumber() * 4 / 3);
        for (Couple<FormalObject, FormalAttribute> couple : context) {
            FormalObject fo = couple.first();
            if (objectSet.contains(fo)) {
                FormalAttribute fa = couple.second();
                BitSetIntent intent = objToIntent.get(fo);
                BitSetExtent extent = attrToExtent.get(fa);
                if (intent == null) {
                    intent = new BitSetIntent(attributeDomain);
                    objToIntent.put(fo, intent);
                }
                intent.add(fa);
                if (extent == null) {
                    extent = new BitSetExtent(objectDomain);
                    attrToExtent.put(fa, extent);
                }
                extent.add(fo);
                size++;
            }
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.alpha.util.Relation#attributeIterator()
     */
    public Iterator<FormalAttribute> attributeIterator() {
        return attributeSet.iterator();
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.alpha.util.Relation#contains(lattice.util.concept.FormalObject,
     *      lattice.util.concept.FormalAttribute)
     */
    public boolean contains(FormalObject obj, FormalAttribute att) {
        Intent intent = objToIntent.get(obj);
        if (intent == null) {
            return false;
        }
        return intent.contains(obj);
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.alpha.util.Relation#contains(lattice.util.concept.FormalAttribute)
     */
    public boolean contains(FormalAttribute fa) {
        return attributeSet.contains(fa);
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.alpha.util.Relation#contains(lattice.util.concept.FormalObject)
     */
    public boolean contains(FormalObject fo) {
        return objectSet.contains(fo);
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.alpha.util.Relation#getAttributesNumber()
     */
    public int getAttributesNumber() {
        return attributeSet.size();
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.alpha.util.Relation#getLattice()
     */
    public CompleteConceptLattice getLattice() {
        return lattice;
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.alpha.util.Relation#getObjectsNumber()
     */
    public int getObjectsNumber() {
        return objectSet.size();
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.alpha.util.Relation#getRelationName()
     */
    public String getName() {
        return relName;
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.alpha.util.Relation#iterator()
     */
    public Iterator<Couple<FormalObject, FormalAttribute>> iterator() {
        return new ObjToIntentMapIterator(objToIntent);
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.alpha.util.Relation#objectIterator()
     */
    public Iterator<FormalObject> objectIterator() {
        return objectSet.iterator();
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.alpha.util.Relation#size()
     */
    public int size() {
        return size;
    }

    public ArrayHashSet<FormalAttribute> getAttributes() {
        return attributeSet;
    }

    public ArrayHashSet<FormalAttribute> getAttributesDomain() {
        return attributeDomain;
    }

    public ArrayHashSet<FormalObject> getObjects() {
        return objectSet;
    }

    public ArrayHashSet<FormalObject> getObjectsDomain() {
        return objectDomain;
    }

    public BitSetExtent getExtent(FormalAttribute fa) {
        return attrToExtent.get(fa);
    }

    public BitSetIntent getIntent(FormalObject fo) {
        return objToIntent.get(fo);
    }

    public void setLattice(CompleteConceptLattice lattice) {
        this.lattice = lattice;
    }

    public void setName(String newName) {
        this.relName = newName;
    }

}
