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

import java.util.Comparator;

/**
 * An OrderedSet whose elements order is further explicited by an indexing 
 * of its elements. 
 * 
 * This interface does not require that succesive elements do have successive
 * index, it is only required that the ordering of the elements corresponds 
 * to the order of their index. 
 * Element removal does not change the elements order and re-insertion
 * of an element previously removed should not change its position with respect
 * to elements which were contained before removal, furthermore, removed elements
 * must remain comparable with the other elements of the set. 
 * 
 * 
 * @author Marc Champesme
 * @since 15 december 2005
 * @version 30 december 2005
 */
public interface IndexedSet<E> extends OrderedSet<E> {
    /*@
      @ public invariant (\forall int i; i >= 0 && i < theList.int_size();
      @                         indexOf(theList.get(i)) >= i);
      @*/
    
    /*@ public normal_behavior
      @ ensures \result <==> (\exists Object o; contains(o); indexOf(o) == index);
      @ ensures (index < 0) ==> !\result;
      public pure model boolean indexInRange(int index);
      @*/

    /*@ also
      @ public normal_behavior
      @ requires contains(o1) && contains(o2);
      @ ensures \result <==> (indexOf(o1) < indexOf(o2));
      public pure model boolean lesserThan(Object o1, Object o2);
      @*/

    /**
     * @see orderedset.OrderedSet#comparator()
     */
    /*@ also
      @ ensures \result instanceof IndexedSetComparator;
      @*/
    public Comparator<? super E> comparator();
    
    /**
     * Returns the element with the specified index in this set or null
     * if this set does not contains any element with this index.
     * 
     * @param index
     *            index of element to return.
     * @return the element with the specified index in this list or null
     * if there is not any element associated with this index
     * @throws IndexOutOfBoundsException -
     *             if the index is out of range (optional).
     */
    /*@
      @ requires indexInRange(index);
      @ ensures indexOf(\result) == index;
      @ ensures contains(\result);
      @ also
      @ signals_only java.lang.IndexOutOfBoundsException;
      @ signals (java.lang.IndexOutOfBoundsException) !indexInRange(index);
      @ pure
      @*/
    public E get(int index);

    /**
     * Returns the index of the specified element, or -1 if this set does not
     * contain this element. More formally, returns the (unique) index i such
     * that o.equals(get(i)), or -1 if there is no such index.
     * 
     * @param o
     *            element to search for.
     * @return the index in this set of the specified element, or -1 if this set
     *         does not contain this element.
     */
    /*@
      @ requires !this.containsNull ==> o != null;
      @ requires (o == null) || \typeof(o) <: this.elementType;
      @ ensures indexInRange(\result) || (\result == -1);
      @ ensures contains(o) <==> (\result >= 0);
      @ ensures (\result == -1) <==> !contains(o);
      @ ensures (indexInRange(\result) && get(\result) == null) ==> o == null;
      @ ensures (indexInRange(\result) && get(\result) != null) ==> get(\result).equals(o);
      @ pure
      @*/
    public int indexOf(Object o);
}
