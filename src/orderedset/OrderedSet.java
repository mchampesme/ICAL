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
import java.util.Comparator;
import java.util.Iterator;
import java.util.Set;

//@ import java.util.Iterator;
//@ import java.util.List;
//@ import org.jmlspecs.models.JMLEqualsSet;
//@ import org.jmlspecs.models.JMLEqualsSequence;

/**
 *  A set that further guarantees that its iterator will traverse the set in
 *  ascending element order. Like SortedSet, this order must be "consistent with
 *  equals". But unlike SortedSet, it is not required that the elements be
 *  comparable in the same way as for SortedSet (i.e. it is not required that
 *  the elements implements the Comparable interface nor that they be accepted
 *  by any Comparator, except by the comparator provided by this class). The
 *  order could be, for instance, defined by the insertion order, thus allowing
 *  different OrderedSet to define different orders for the same elements, however
 *  it is strongly required that a given instance do not change the order of its
 *  elements, in particular, an element which is removed and then inserted again
 *  must be inserted in the same place. 
 *
 * @author     Marc Champesme
 * @version    29 décembre 2005
 * @since      15 décembre 2005
 */
public interface OrderedSet<E> extends Set<E> {
	/*@
      @ public invariant theSet.int_size() == theList.int_size();
      @*/
    
    /*@
      @ public model instance JMLEqualsSequence theList;
      @ public represents theSet <- theList.toSet();
      @ private represents theList <- JMLEqualsSequence.convertFrom(this);
      @
      @*/
    
    /*@ public normal_behavior
      @     ensures \result <==> ((OrderedSetComparator) comparator()).comparable(o1, o2);
      public pure model boolean comparable(Object o1, Object o2) {
            OrderedSetComparator cmp = (OrderedSetComparator) comparator();
            return cmp.comparable(o1, o2);
      }
      @*/
    
    /*@ public normal_behavior
      @     requires comparable(o1, o2);
      @     ensures \result <==> (comparator().compare(o1, o2) < 0);
      public pure model boolean lesserThan(Object o1, Object o2) {
           return comparator().compare(o1, o2) < 0;
      }
      @*/
    
	/**
	 *  Returns true if the specified element may be added to this set.
	 *
	 * @param  obj  object whose acceptability is to be tested.
	 * @return      true if the specified element may be added to this set.
	 */
	/*@
	  @     requires contains(obj);
      @     ensures \result;
      @ also
      @     requires obj == null;
      @     ensures \result <==> this.containsNull;
      @ pure
      @*/
	public boolean isAcceptableElement(E obj);

    /**
     * Returns the comparator associated with this ordered set.
     * @return the comparator associated with this ordered set.
     */
    /*@
      @ ensures \result instanceof OrderedSetComparator;
      @ pure
      @*/
    public Comparator<? super E> comparator();
    
    /**
     * Returns an iterator over the elements in this set. The elements are returned in the order 
     * specified by the comparator.
     * 
     * @return an iterator over the elements in this set.
     *
     * @see java.util.Set#iterator()
     */
    /*@ also
      @ ensures (\forall int i; i >= 0 && i < size(); 
      @             ((containsNull && theList.itemAt(i) == null) ==> (\result.nthNextElement(i) == null))
      @             && ((theList.itemAt(i) != null) ==> \result.nthNextElement(i).equals(theList.itemAt(i))));
      @*/
    public Iterator<E> iterator();


	/**
     * Adds the specified element to this set if it is not already present (optional operation). 
     * More formally, adds the specified element, o, to this set if this set contains no 
     * element e such that (o==null ? e==null : o.equals(e)). If this set already contains the 
     * specified element, the call leaves this set  and the position of the specified
     * element in the sequence of elements unchanged and returns false. In combination with 
     * the restriction on constructors, this ensures that sets never contain duplicate elements.
     * 
     * Only acceptable elements (i.e. elements for which is method isAcceptableElement returns
     * true) are accepted. As required in the specification for Collection.add, tentative 
     * to call this method with a non acceptable element will throw an exception.
     *  
	 * @param  o  element to be added to this set.
	 * @return    true if this set did not already contain the specified element.
	 * @see       java.util.Set#add(java.lang.Object)
     * @throws     UnsupportedOperationException  if the add method is not supported by this set. 
     * @throws ClassCastException  if the class of the specified element prevents it from being added to this set. 
     * @throws NullPointerException  if the specified element is null and this set does not support null elements. 
     * @throws IllegalArgumentException - if the specified element is not an aceptable element.
	 */
	/*@ also
      @ requires isAcceptableElement(o);
      @ ensures theSet.has(o);
      @ also
      @ requires isAcceptableElement(o);
      @ requires contains(o);
      @ assignable \nothing;
      @ ensures !\result;
      @ signals (java.lang.NullPointerException) o == null && !this.containsNull;
      @ signals (java.lang.ClassCastException) o != null && !(\typeof(o) <: this.elementType);
      @ signals (java.lang.IllegalArgumentException) o != null 
      @                                              && (\typeof(o) <: this.elementType) 
      @                                              && !isAcceptableElement(o);
      @*/
	public boolean add(E o);

    /**
     * Adds all of the elements in the specified collection to this set if they're not 
     * already present (optional operation). If the specified collection is also a set,
     * the addAll operation effectively modifies this set so that its value is the 
     * union of the two sets. This operation is garanteed to preserve the order of 
     * the elements which were previously in this ordered set. Elements of the specified
     * collection wich were not previously in this set are added according to the order
     * specified by the comparator of this set or, if they where not comparable with the 
     * elements of this set, they are considered as greater than all the elements currently
     * in this set and added in the order specified by the iterator of the specified collection.
     * The behavior of this operation is unspecified if the 
     * specified collection is modified while the operation is in progress.
     * 
     * Only acceptable elements (i.e. elements for which the method isAcceptableElement returns
     * true) are accepted. As required in the specification for Collection.add, tentative 
     * to call this method with a non acceptable element will throw an exception.

     * @see java.util.Set#addAll(java.util.Collection)
     * @param c collection whose elements are to be added to this set.
     * @return true if this set changed as a result of the call.
     * @throws     UnsupportedOperationException  if the add method is not supported by this set. 
     * @throws ClassCastException  if the class of some element of the specified set 
     * prevents it from being added to this set. 
     * @throws NullPointerException  if some element of the specified set is null and this set does not 
     * support null elements, or if the specified collection is null.
     * @throws IllegalArgumentException if some element of the specified set is not an aceptable element.
    */
    /*@ also
      @ old OrderedSetComparator oldCmp = (OrderedSetComparator) comparator();
      @ requires c != null;
      @ requires (\forall Object o; c.contains(o); isAcceptableElement(o));
      @ {|
      @     requires containsAll(c);
      @     assignable \nothing;
      @     ensures theList.equals(\old(theList));
      @ also
      @     ensures (\forall Object o1, o2; \old(contains(o1)) && c.contains(o2) && !\old(contains(o2));
      @                 \old(comparable(o1, o2)) ==> (lesserThan(o1, o2) <==> \old(lesserThan(o1, o2)))
      @                 && !\old(comparable(o1, o2)) ==> lesserThan(o1, o2));
      @ also
      @     requires c instanceof OrderedSet;
      @     ensures (\forall Object o1, o2; c.contains(o1) && c.contains(o2) && !\old(contains(o1)) && !\old(contains(o2));
      @                 \old(comparable(o1, o2)) ==> (lesserThan(o1, o2) <==> \old(lesserThan(o1, o2)))
      @                 && !\old(comparable(o1, o2)) ==> (lesserThan(o1, o2) <==> ((OrderedSet) c).lesserThan(o1, o2)));
      @ also
      @     requires c instanceof List;
      @     ensures (\forall Object o1, o2; c.contains(o1) && c.contains(o2) && !\old(contains(o1)) && !\old(contains(o2));
      @                 \old(comparable(o1, o2)) ==> (lesserThan(o1, o2) <==> \old(lesserThan(o1, o2)))
      @                 && !\old(comparable(o1, o2)) ==> (lesserThan(o1, o2) <==> (((List) c).indexOf(o1) < ((List) c).indexOf(o2))));
      @ |}
      @ also
      @ signals (java.lang.NullPointerException) c == null || (!this.containsNull && c.contains(null));
      @ signals (java.lang.ClassCastException) c != null && (this.containsNull || !c.contains(null))
      @                                          && (\exists Object o; c.contains(o); o != null && !(\typeof(o) <: this.elementType));
      @ signals (java.lang.IllegalArgumentException) c != null && (this.containsNull || !c.contains(null))
      @                                              && (\forall Object o; c.contains(o); o == null || \typeof(o) <: this.elementType)
      @                                              && (\exists Object o; c.contains(o); !isAcceptableElement(o));
      @*/
    public boolean addAll(Collection<? extends E> c);


    /**
     * Returns true only if the specified set contains the same elements in the
     * same order.
     * 
     * @param set the set with which to compare.
     * @return true only if the specified set contains the same elements in the
     * same order as this ordered set.
     */
    /*@
      @ requires set != null;
      @ {|
      @ ensures \result <==> theSet.equals(set.theSet) && theList.equals(set.theList);
      @ also
      @ requires !equals(set);
      @ ensures !\result;
      @ also
      @ requires equals(set); 
      @ ensures comparator().equals(set.comparator()) ==> \result;
      @ also
      @ old Iterator thisSetIterator = iterator();
      @ old Iterator otherSetIterator = set.iterator();
      @ requires size() == set.size();
      @ ensures \result <==> (\forall int i; i >= 0 && i < size();
      @                 thisSetIterator.nthNextElement(i).equals(otherSetIterator.nthNextElement(i)));
      @ |}
      @ pure
      @*/
    public boolean orderedSetEquals(OrderedSet<?> set);

	/**
	 * @param  o  Description of the Parameter
	 * @return    Description of the Return Value
	 * @see       java.util.Set#contains(java.lang.Object)
	 */
	/*@ also
      @ ensures !isAcceptableElement(o) ==> !\result;
      @ ensures \result ==> isAcceptableElement(o);
      @*/
	public boolean contains(Object o);
}

