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

import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.Map.Entry;

import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;

/**
 * @author marc
 */
public class ObjToIntentMapIterator implements
        Iterator<Couple<FormalObject, FormalAttribute>> {
    private Iterator<? extends Entry<FormalObject, ? extends Set<FormalAttribute>>> mapIter;

    private Iterator<FormalAttribute> attrIter;

    private boolean hasMoreElements;

    private FormalObject currentFObject;

    public ObjToIntentMapIterator(
                                  Map<FormalObject, ? extends Set<FormalAttribute>> map) {
        mapIter = map.entrySet().iterator();
        hasMoreElements = true;
        // @ assume attrIter == null;
        nextIterator();
        // @ assume (hasMoreElements && currentFObject != null
        // @ && attrIter != null && attrIter.hasNext())
        // @ || !hasMoreElements;
    }

    /**
     * 
     */
    /*
     * @ @ requires mapIter != null; @ requires hasMoreElements; @ requires
     * attrIter == null || !attrIter.hasNext(); @ ensures hasMoreElements ==>
     * (attrIter != null @ && attrIter != \old(attrIter) @ && attrIter.hasNext() @ &&
     * currentFObject != null @ && currentFObject != \old(currentFObject)); @
     */
    private void nextIterator() {
        while (hasMoreElements && (attrIter == null || !attrIter.hasNext())) {
            hasMoreElements = mapIter.hasNext();
            if (hasMoreElements) {
                Entry<FormalObject, ? extends Set<FormalAttribute>> nextEntry = mapIter
                        .next();
                // @ assume nextEntry != null;
                // @ assume nextEntry.getKey() != null;
                currentFObject = nextEntry.getKey();
                // @ assume nextEntry.getValue() != null;
                attrIter = nextEntry.getValue().iterator();
            }
            // @ assume (hasMoreElements && attrIter != null && currentFObject
            // != null)
            // @ || !hasMoreElements;
        }
        // @ assume (hasMoreElements && currentFObject != null
        // @ && attrIter != null && attrIter.hasNext())
        // @ || !hasMoreElements;
    }

    public boolean hasNext() {
        return hasMoreElements;
    }

    public Couple<FormalObject, FormalAttribute> next() {
        if (!hasMoreElements) {
            throw new NoSuchElementException();
        }
        // @ assume hasMoreElements && attrIter != null && attrIter.hasNext();
        FormalAttribute fa = attrIter.next();
        if (!attrIter.hasNext()) {
            nextIterator();
        }
        return new Couple<FormalObject, FormalAttribute>(currentFObject, fa);
    }

    public void remove() {
        throw new UnsupportedOperationException();
    }

}
