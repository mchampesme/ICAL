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
package orderedset;

import java.util.BitSet;
import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * @author     Marc Champesme
 * @version    22 décembre 2005
 * @since      15 décembre 2005
 */
public class BitSetDOSIterator<E> implements Iterator<E> {
	//@ private represents moreElements <- (remainingEltCount > 0);
	private BitSet bitSet;
	private IndexedSet<E> domain;
	private int lastViewed;
	//@ in objectState;
	private int remainingEltCount;
	//@ in moreElements;
	private boolean illegalRemoveState; //@ in objectState;


	/**
	 *  Constructor for the BitSetDOSIterator object
	 *
	 * @param  domain     Description of the Parameter
	 * @param  bitSet     Description of the Parameter
	 * @param  nbElement  Description of the Parameter
	 */
	public BitSetDOSIterator(IndexedSet<E> domain, BitSet bitSet, int nbElement) {
        //@ set elementType = \type(java.lang.Object);
        //@ set returnsNull = false;
		this.bitSet = bitSet;
		this.domain = domain;
		lastViewed = -1;
		remainingEltCount = nbElement;
		illegalRemoveState = true;
        //@ set remove_called_since = illegalRemoveState;
	}


	/**
	 *  Returns true if the iteration has more elements. (In other words, returns
	 *  true if next would return an element rather than throwing an exception.)
	 *
	 * @return    true if the iterator has more elements.
	 * @see       java.util.Iterator#hasNext()
	 */
	public boolean hasNext() {
		return remainingEltCount > 0;
	}


	/**
	 *  Returns the next element in the iteration.
	 *
	 * @return                          the next element in the iteration.
	 * @see                             java.util.Iterator#next()
	 * @throws  NoSuchElementException  if this iteration has no more elements.
	 */
	public E next() {
		lastViewed = bitSet.nextSetBit(lastViewed + 1);
		if (lastViewed == -1) {
			throw new NoSuchElementException();
		}
		illegalRemoveState = false;
         //@ set remove_called_since = illegalRemoveState;
		remainingEltCount--;
		return domain.get(lastViewed);
	}


	/**
	 *  Removes from the underlying collection the last element returned by the
	 *  iterator (optional operation). This method can be called only once per call
	 *  to next. The behavior of an iterator is unspecified if the underlying
	 *  collection is modified while the iteration is in progress in any way other
	 *  than by calling this method.
	 *
	 * @see                                    java.util.Iterator#remove()
	 * @throws  UnsupportedOperationException  if the remove operation is not
	 *      supported by this Iterator.
	 * @throws  IllegalStateException          if the next method has not yet been
	 *      called, or the remove method has already been called after the last
	 *      call to the next method.
	 */
	public void remove() {
		if (illegalRemoveState) {
			throw new IllegalStateException();
		}
		bitSet.clear(lastViewed);
		illegalRemoveState = true;
         //@ set remove_called_since = illegalRemoveState;
	}

}

