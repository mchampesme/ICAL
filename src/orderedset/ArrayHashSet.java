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

import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

//@ import org.jmlspecs.models.JMLEqualsSequence;

/**
 * Fixed size array implementation of an ImmutIndexedSet, which does not
 * support null elements.
 * 
 * @author Marc Champesme
 * @since 15 december 2005
 * @version 30 december 2005
 */
public class ArrayHashSet<E> extends AbstractImmutSet<E> implements ImmutIndexedSet<E> {
    
    /*@
      @ public represents nullElementsSupported <- false;
      @ {
      @     set containsNull = false;
      @ }
      @ private represents theList <-  JMLEqualsSequence.convertFrom(indexedContent, eltToIndexMap.size());
      @*/

    /*@ also
      @ public normal_behavior
      @ ensures \result <==> (index >= 0 && index < size());
      public pure model boolean indexInRange(int index) {
          return index >= 0 && index < size();
      }
      @*/

    private E[] indexedContent;
    private Map<E, Integer> eltToIndexMap;
    private int cachedHashCode;
    private OrderedSetComparator<E> theComparator;
    
    /**
     * Constructs an empty set. 
     */
    /*@
      @ ensures isEmpty();
      @*/
    @SuppressWarnings("unchecked")
    public ArrayHashSet() {
        //@ set containsNull = false;
        //@ set elementType = \type(java.lang.Object);
        indexedContent = (E[]) new Object[0];
        eltToIndexMap = Collections.emptyMap();
        cachedHashCode = 1;
        theComparator = new IndexedSetComparator<E>(this);
    }
    
    /**
     * Constructs a list containing the elements of the specified collection, 
     * in the order they are returned by the collection's iterator.
     * 
     * @param c the collection whose elements are to be placed into this list.
     */
    /*@
      @ old Iterator collecIter = c.iterator();
      @ requires c != null;
      @ requires !c.containsNull || !contains(null);
      @ ensures containsAll(c);
      @ ensures this.size() <= c.size();
      @ ensures (\forall int i, j; 0 <= i && i < j && j < c.size(); 
      @         lesserThan(collecIter.nthNextElement(i), collecIter.nthNextElement(j)));
      @*/
    @SuppressWarnings("unchecked")
    public ArrayHashSet(Collection<? extends E> c) {
        //@ set containsNull = false;
        //@ set elementType = \type(java.lang.Object);
        Set<? extends E> auxSet;
        if (c instanceof Set) {
            auxSet = (Set<? extends E>) c;
        } else {
            // to remove duplicates
            auxSet = new LinkedHashSet<E>(c);
        }
        indexedContent = (E[]) new Object[auxSet.size()];
        eltToIndexMap = new HashMap<E,Integer>(auxSet.size() * 4 / 3);
        Iterator<? extends E> collIter = auxSet.iterator();
        int index = 0;
        cachedHashCode = 1;
        while (collIter.hasNext()) {
            E obj = collIter.next();
            eltToIndexMap.put(obj, index);
            indexedContent[index] = obj;
            cachedHashCode += obj.hashCode();
            index++;
        }
        theComparator = new IndexedSetComparator<E>(this);
    }
    
    /**
     * Returns true if this set contains the specified element. 
     * More formally, returns true if and only if this set contains 
     * an element e such that (o==null ? e==null : o.equals(e)).
     * 
     * @param o element whose presence in this set is to be tested.
     * @return true if this set contains the specified element.
     */
    public boolean contains(Object o) {
        return eltToIndexMap.containsKey(o);
    }
    
    /**
     * Returns an iterator over the elements in this set. The elements 
     * are returned in the order specified by the comparator.
     * 
     * @return an iterator over the elements in this set.
     *
     * @see java.util.Set#iterator()
     */
    public Iterator<E> iterator() {
        return new ArrayReadOnlyIterator<E>(indexedContent, size());
    }

    /**
     * Returns the number of elements in this set (its cardinality). If this 
     * set contains more than Integer.MAX_VALUE elements, returns Integer.MAX_VALUE.
     * 
     * @return the number of elements in this set (its cardinality).
     * @see java.util.AbstractCollection#size()
     */
    public int size() {
        return eltToIndexMap.size();
    }

    /**
     * Returns the element with the specified index in this set.
     * 
     * @param index
     *            index of element to return.
     * @return the element with the specified index in this list.
     * @throws IndexOutOfBoundsException -
     *             if the index is out of range (index < 0 || index >= size()).
     * @see orderedset.IndexedSet#get(int)
     */
    /*@ also
      @ ensures \result.equals(theList.get(index));
      @*/
    public E get(int index) {
        return (E) indexedContent[index];
    }

    /**
     * Returns the index of the specified element, or -1 if this set does not
     * contain this element. More formally, returns the (unique) index i such
     * that o.equals(get(i)), or -1 if there is no such index.
     * 
     * @param o
     *            element to search for.
     * @return the index in this set of the specified element, or -1 if this set
     *         does not contain this element.
     * @see orderedset.IndexedSet#indexOf(java.lang.Object)
     */
    public int indexOf(Object o) {
        Integer index = eltToIndexMap.get(o);
        if (index == null) {
            return -1;
        }
        return index.intValue();
    }
    
    /**
     * Returns the hash code value for this set. The hash code of a set 
     * is defined to be the sum of the hash codes of the elements in the set, 
     * where the hashcode of a null element is defined to be zero. 
     * This ensures that s1.equals(s2) implies that s1.hashCode()==s2.hashCode() 
     * for any two sets s1 and s2, as required by the general contract of 
     * the Object.hashCode method.
     * 
     * @return the hash code value for this set.
     */
    public int hashCode() {
        return cachedHashCode;
    }

    /**
     * Compares the specified object with this set for equality. 
     * Returns true if the specified object is also a set, the two sets have 
     * the same size, and every member of the specified set is contained in 
     * this set (or equivalently, every member of this set is contained in 
     * the specified set). This definition ensures that the equals method 
     * works properly across different implementations of the set interface.
     * 
     * @param o Object to be compared for equality with this set. 
     * @return true if the specified Object is equal to this set.
     * @see java.util.AbstractSet#equals(java.lang.Object)
     */
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof Set<?>)) {
            return false;
        }
        Set<?> asSet = (Set<?>) o;
        if (size() != asSet.size()) {
            return false;
        }
        boolean allPresents = true;
        for (int i = 0; i < size() && allPresents; i++) {
            allPresents = asSet.contains(indexedContent[i]);
        }
        return allPresents;
    }

    /**
     * Returns a new Set which contains only the elements in this 
     * set that are contained in the specified collection. In other words, 
     * construct the set obtained by removing from this set all of its elements
     * that are not contained in the specified collection. This operation return a 
     * new set whose value is the intersection of this set with the specified 
     * collection considered as a set. It may be used as
     * an immutable version of the retainAll operation.
     * 
     * @param c collection that defines which elements the returned set will retain from this set.
     * @return a Set which is the intersection of the two sets
     * @see orderedset.ImmutSet#intersection(java.util.Collection)
     */
    /*@ also
      @ requires c != null;
      @ ensures \result instanceof ArrayHashSet;
      @*/
    public Set<E> intersection(Collection<?> c) {
        ArrayHashSet<E> newSet = new ArrayHashSet<E>();
        if (isEmpty() || c.isEmpty()) {
            return newSet;
        }
        if (this == c) {
            return this;
        }
        int maxSize = Math.min(size(), c.size());
        @SuppressWarnings("unchecked")
        E[] newIndexedContent = (E[]) new Object[maxSize];
        Map<E,Integer> newEltToIndexMap = new HashMap<E,Integer>(maxSize * 4 / 3);
        int newHashCode = 1;
        int index = 0;
        for (int i = 0; i < size(); i++) {
            if (c.contains(indexedContent[i])) {
                newIndexedContent[index] = indexedContent[i];
                newEltToIndexMap.put(indexedContent[i], index);
                newHashCode += indexedContent[i].hashCode();
                index++;
            }
        }
        newSet.indexedContent = newIndexedContent;
        newSet.eltToIndexMap = newEltToIndexMap;
        newSet.cachedHashCode = newHashCode;
        return newSet;
    }

    /**
     * Returns a new set that contains all the elements that 
     * are in either this or the given argument. Elements of the returned set 
     * which are comparable according to this set are ordered
     * as in this set, other elements are ordered as specified by the iterator
     * of the specified collection.
     * @param c collection that defines which elements the returned set will contain 
     * in addition to the elements of this set.
     * @return a Set which is the union of the two sets
     */
    /*@ also
    @ requires c != null;
    @ ensures \result instanceof ArrayHashSet;
    @*/
    public Set<E> union(Collection<? extends E> c) {
        if (c.isEmpty() || this == c) {
            return this;
        }
        if (isEmpty()) {
            return new ArrayHashSet<E>(c);
        }
        ArrayHashSet<E> newSet = new ArrayHashSet<E>();
        int maxSize = size() + c.size();
        @SuppressWarnings("unchecked")
        E[] newIndexedContent = (E[]) new Object[maxSize];
        Map<E,Integer> newEltToIndexMap = new HashMap<E,Integer>(maxSize * 4 / 3);
        int newHashCode = 1;
        int index = 0;
        for (; index < size(); index++) {
            newIndexedContent[index] = indexedContent[index];
            newEltToIndexMap.put(indexedContent[index], index);
            newHashCode += indexedContent[index].hashCode();
        }
        Iterator<? extends E> setIter = c.iterator();
        while (setIter.hasNext()) {
            E obj = setIter.next();
            if (!contains(obj)) {
                newIndexedContent[index] = obj;
                newEltToIndexMap.put(obj, index);
                newHashCode += obj.hashCode();
                index++;
            }
        }
        newSet.indexedContent = newIndexedContent;
        newSet.eltToIndexMap = newEltToIndexMap;
        newSet.cachedHashCode = newHashCode;
        return newSet;
    }

    /**
     * Returns a new set that contains all the elements that are in 
     * this but not in the given argument.
     * 
     * @param c collection that defines which elements the returned set will 
     * not retain from this set.
     * @return a new set that represents the set difference of this with the 
     * specified collection of elements.
     */
    /*@ also
    @ requires c != null;
    @ ensures \result instanceof ArrayHashSet;
    @*/
    public Set<E> difference(Collection<?> c) {
        ArrayHashSet<E> newSet = new ArrayHashSet<E>();
        if (isEmpty() || (this == c)) {
            return newSet;
        }
        if (c.isEmpty()) {
            return this;
        }
        int maxSize = size();
        @SuppressWarnings("unchecked")
        E[] newIndexedContent = (E[]) new Object[maxSize];
        Map<E,Integer> newEltToIndexMap = new HashMap<E,Integer>(maxSize * 4 / 3);
        int newHashCode = 1;
        int index = 0;
        for (int i = 0; i < size(); i++) {
            if (!c.contains(indexedContent[i])) {
                newIndexedContent[index] = indexedContent[i];
                newEltToIndexMap.put(indexedContent[i], index);
                newHashCode += indexedContent[i].hashCode();
                index++;
            }
        }
        newSet.indexedContent = newIndexedContent;
        newSet.eltToIndexMap = newEltToIndexMap;
        newSet.cachedHashCode = newHashCode;
        return newSet;
    }
    
    /**
     * Trims the capacity of this ArrayHashSet instance to be the list's current size,
     * if needed. 
     * An application can use this operation to minimize the storage of an ArrayHashSet 
     * instance which results from an intersection, union or difference operation.
     */
    public void trimToSize() {
        if (size() < indexedContent.length) {
            @SuppressWarnings("unchecked")
            E[] newindexedContent = (E[]) new Object[size()];
            Map<E,Integer> newMap = new HashMap<E,Integer>(eltToIndexMap);
            eltToIndexMap = newMap;
            System.arraycopy(indexedContent, 0, newindexedContent, 0, size());
            indexedContent = newindexedContent;
        }
    }


    /**
     * @see orderedset.OrderedSet#isAcceptableElement(java.lang.Object)
     */
    /*@ also
      @ ensures \result;
      @*/
    public boolean isAcceptableElement(E obj) {
        return true;
    }

    /**
     * Returns the comparator associated with this ordered set.
     * 
     * @return the comparator associated with this ordered set.
     * @see orderedset.OrderedSet#comparator()
     */
    /*@ also
      @ ensures \result instanceof IndexedSetComparator;
      @*/
    public Comparator<E> comparator() {
        return theComparator;
    }

    /**
     * Returns true only if the specified set contains the same elements in the
     * same order.
     * 
     * @param set the set with which to compare.
     * @return true only if the specified set contains the same elements in the
     * same order as this ordered set.
     */
    public boolean orderedSetEquals(OrderedSet<?> set) {
        if (this == set) {
            return true;
        }
        if (size() != set.size()) {
            return false;
        }
        boolean allEquals = true;
        Iterator<?> iter = set.iterator();
        int i = 0;
        while (i < size() && iter.hasNext() && allEquals) {
            allEquals = indexedContent[i].equals(iter.next());
            i++;
        }
        return allEquals;
    }
}
