package lattice.util.relation;

import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import lattice.alpha.util.Couple;
import lattice.util.concept.AbstractFormalAttributeValue;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;

public class MatrixBinaryRelationIterator implements
        Iterator<Couple<FormalObject, FormalAttribute>> {
    private List<FormalObject> objectSet;

    private List<FormalAttribute> attributeSet;

    private Iterator<List<AbstractFormalAttributeValue>> objIter;

    private Iterator<AbstractFormalAttributeValue> attrIter;

    private int objIndex;

    private int attrIndex;
    
    private boolean hasMoreElements;

    public MatrixBinaryRelationIterator(
                                  List<FormalObject> objectSet,
                                  List<FormalAttribute> attributeSet,
                                  Iterator<List<AbstractFormalAttributeValue>> objIter) {
        this.objectSet = objectSet;
        this.attributeSet = attributeSet;
        this.objIter = objIter;
        hasMoreElements = objIter.hasNext();
        if (hasMoreElements) {
            attrIter = objIter.next().iterator();
            nextTrueValue();
        } 
    }

    /**
     * 
     */
    private void nextTrueValue() {
        boolean found = false;
        while (hasMoreElements && !found) {
            while (attrIter.hasNext() && !found) {
                found = attrIter.next().isTrue();
                if (!found)
                    attrIndex++;
            }
            //@ assume !hasMoreElements
            if (!found) {
                //@ assume !attrIter.hasNext();
                hasMoreElements = objIter.hasNext();
                if (hasMoreElements) {
                    attrIter = objIter.next().iterator();
                    objIndex++;
                }
            }
            //@ assume (!found) || (found && hasMoreElements);
        } 
        //@ assume (!hasMoreElements && !found) || (found && hasMoreElements);
    }
    public boolean hasNext() {
        return hasMoreElements;
    }

    public Couple<FormalObject, FormalAttribute> next() {
        if (!hasMoreElements) {
            throw new NoSuchElementException();
        }
        FormalObject fo = objectSet.get(objIndex);
        FormalAttribute fa = attributeSet.get(attrIndex);
        nextTrueValue();
        return new Couple<FormalObject, FormalAttribute>(fo, fa);
    }

    public void remove() {
        throw new UnsupportedOperationException();
    }

}
