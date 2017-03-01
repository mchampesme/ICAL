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

import lattice.util.concept.Concept;
import lattice.util.structure.Node;

/**
 * @author marc
 */
public class NodeListByIntentDecIterator implements Iterator<Node<Concept>> {
    /*@
      @ private represents moreElements <- currentIterator.moreElements;
      @*/

    private int currentIntentSize; //@ in objectState;

    private int minIntentSize;

    private Iterator<Node<Concept>> currentIterator; //@ in objectState;

    private Iterator<Node<Concept>> removeIterator; //@ in objectState;

    private NodeListByIntent list;

    public NodeListByIntentDecIterator(NodeListByIntent aList) {
        list = aList;
        minIntentSize = list.minIntentSize();
        currentIntentSize = list.maxIntentSize();
        currentIterator = list.iterator(currentIntentSize);
        nextIterator();
        removeIterator = currentIterator;
    }

    /**
     * 
     */
    /*@
      @ assignable objectState;
      @*/
    private void nextIterator() {
        while (!currentIterator.hasNext() && currentIntentSize > minIntentSize) {
            currentIntentSize--;
            currentIterator = list.iterator(currentIntentSize);
        }
    }

    /*@
      @ 
      @ 
      @ 
      @*/
    public boolean hasNext() {
        return currentIterator.hasNext();
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.util.Iterator#next()
     */
    public Node<Concept> next() {
        Node<Concept> nextObject = currentIterator.next();
        removeIterator = currentIterator;
        nextIterator();
        return nextObject;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.util.Iterator#remove()
     */
    public void remove() {
        removeIterator.remove();
    }
}
