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

import java.util.Arrays;
import java.util.Iterator;

/**
 * @author     Marc Champesme
 * @version    22 décembre 2005
 * @since      15 décembre 2005
 */
public class ArrayReadOnlyIterator<E> implements Iterator<E> {
	private E[] theArray;
	private int current; //@ in moreElements;
	private int theSize;
    //@ private represents moreElements <- (current < theSize);
    
    
    /*@ 
     public pure model boolean hasNext(int n) {
             return (current + n) < theSize;
     }
      @*/
    
    /*@ 
      public pure model Object nthNextElement(int n) {
          return theArray[current + n];
      }
      @*/
    

	/**
	 * @param  content
	 * @param  size
	 */
    /*@
      @ requires content != null;
      @ requires size >= 0;
      @ requires content.length >= size;
      @ requires (\forall int i; i >= 0 && i < size;
      @                                         content[i] != null);
      @ ensures (size > 0) ==> moreElements;
      @ ensures (\forall int i; i >= 0 && i < size; 
      @             nthNextElement(i) == content[i]);
      @*/
	public ArrayReadOnlyIterator(E[] content, int size) {
        //@ set elementType = \type(java.lang.Object);
        //@ set returnsNull = false;
		theArray = content;
		current = 0;
		theSize = size;
	}


	/**
	 *  Description of the Method
	 *
	 * @return    Description of the Return Value
	 * @see       java.util.Iterator#hasNext()
	 */
	public boolean hasNext() {
		return current < theSize;
	}


	/**
	 *  Description of the Method
	 *
	 * @return    Description of the Return Value
	 * @see       java.util.Iterator#next()
	 */
	public E next() {
		E nextElem = theArray[current];
		current++;
		return nextElem;
	}


	/**
	 *  Unsupported operation.
	 *
	 * @throws  UnsupportedOperationException  always.
	 * @see                                    java.util.Iterator#remove()
	 */
	public void remove() {
		throw new UnsupportedOperationException();
	}

    public String toString() {
        String retString = "orderedset.ArrayReadOnlyIterator:";
        retString += Arrays.asList(theArray).toString();
        retString += "@" + String.valueOf(current) + "/" + String.valueOf(theSize);
        return retString;
    }
}

