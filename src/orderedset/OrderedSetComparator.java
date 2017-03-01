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
//@ import java.util.Iterator;

/**
 * A comparison function, which reflects the order of a specific OrderedSet called the reference set
 * of this comparator, i.e. the order in which the elements are returned by an iterator of this set.
 * For this comparator, an element is lesser than another element if and only if the lesser element 
 * would be returned before the other, if both elements were contained in the reference set.
 * 
 * Only elements which are comparable in the sens of the comparable method (i.e. couples
 * of elements for which the comparable method returns true), are garanteed to return a correct
 * result when tested with the compare method. A minimal requirement is
 * that all elements contained in the reference set be comparable.
 * 
 * Modifications to the reference set may change the result returned by the comparable method:
 * elements removed from the reference set may become uncomparable and elements added to the set
 * may become comparable. However, implementations of this interface must garantee that 
 * comparable elements which remain comparable after modifying the reference set yield to the same 
 * result of the comparison function: it is recommended that modifications to the reference
 * set do not change the order of the elements. 
 * Thus, proper use of an OrderedSetComparator over a mutable set involve getting a new comparator 
 * instance before each use.
 * 
 * @author Marc Champesme
 * @since 28 december 2005
 * @version 29 december 2005
 */
public interface OrderedSetComparator<E> extends Comparator<E> {
    /*@
      @ public model instance OrderedSet referenceSet;
      @
      @ public invariant (\forall Object o1, o2; referenceSet.contains(o1) && referenceSet.contains(o1);
      @                             comparable(o1, o2));
      @*/

    /**
     * @param o1
     * @param o2
     * @return
     */
    /*@
      @ requires referenceSet.contains(o1) && referenceSet.contains(o1);
      @ ensures \result;
      @ also
      @ requires o1 == o2;
      @ ensures \result;
      @ pure
      @*/
    public boolean comparable(E o1, E o2);

    /**
     * Compares its two arguments for order. Returns a negative integer, zero,
     * or a positive integer as the first argument is less than, equal to, or
     * greater than the second. 
     * The implementor must ensure that sgn(compare(x,
     * y)) == -sgn(compare(y, x)) for all x and y. (This implies that compare(x,
     * y) must throw an exception if and only if compare(y, x) throws an
     * exception.) 
     * The implementor must also ensure that the relation is
     * transitive: ((compare(x, y)>0) && (compare(y, z)>0)) implies compare(x,
     * z)>0. 
     * Finally, the implementer must ensure that compare(x, y)==0 implies
     * that sgn(compare(x, z))==sgn(compare(y, z)) for all z. It is generally
     * the case, but not strictly required that (compare(x, y)==0) ==
     * (x.equals(y)). Generally speaking, any comparator that violates this
     * condition should clearly indicate this fact. The recommended language is
     * "Note: this comparator imposes orderings that are inconsistent with
     * equals."
     * 
     * @param o1 the first object to be compared.
     * @param o2 the second object to be compared.
     * @return a negative integer, zero, or a positive integer as the first argument 
     * is less than, equal to, or greater than the second. 
     * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
     * @throws ClassCastException - if the arguments are not comparable.
     */
    /*@ also
      @ requires comparable(o1, o2);
      @ requires o1 != null;
      @ ensures (\result == 0) <==> o1.equals(o2);
      @ ensures (\result == 0) <==> (compare(o2, o1) == 0);
      @ ensures (\result < 0) <==> (compare(o2, o1) > 0);
      @ ensures (\result > 0) <==> (compare(o2, o1) < 0);
      @ also
      @ requires comparable(o1, o2);
      @ requires o1 == null;
      @ ensures (\result == 0) <==> (o2 == null);
      @ also
      @ requires o1 != null && o2 != null;
      @ requires referenceSet.contains(o1) && referenceSet.contains(o2);
      @ ensures (referenceSet.theList.indexOf(o1) < referenceSet.theList.indexOf(o2))
      @         <==> \result < 0;
      @ ensures (referenceSet.theList.indexOf(o1) > referenceSet.theList.indexOf(o2))
      @         <==> \result > 0;
      @*/
    public int compare(E o1, E o2);

    /**
     * Returns true only if the specified Object is also a comparator and it
     * imposes the same ordering as this comparator. Thus, comp1.equals(comp2)
     * implies that sgn(comp1.compare(o1, o2))==sgn(comp2.compare(o1, o2)) for
     * every object reference o1 and o2.
     * 
     * @param obj
     *            the reference object with which to compare.
     * @return true only if the specified object is also a comparator and it
     *         imposes the same ordering as this comparator.
     * @see java.util.Comparator#equals(java.lang.Object)
     */
    /*@ also
      @ requires !(obj instanceof Comparator);
      @ ensures !\result;
      @ also
      @ requires obj instanceof OrderedSetComparator;
      @ ensures \result ==> (\forall Object o1, o2; ;
      @                 comparable(o1, o2) <==> ((OrderedSetComparator) obj).comparable(o1, o2));
      @ ensures \result ==> (\forall Object o1, o2; comparable(o1, o2);
      @                 ((compare(o1, o2) < 0) <==> (((OrderedSetComparator) obj).compare(o1, o2) < 0))
      @                 && ((compare(o1, o2) > 0) <==> (((OrderedSetComparator) obj).compare(o1, o2) > 0))
      @                 && ((compare(o1, o2) == 0) <==> (((OrderedSetComparator) obj).compare(o1, o2) == 0)));
      @ also
      @ requires obj instanceof OrderedSetComparator;
      @ requires referenceSet.equals(((OrderedSetComparator) obj).referenceSet);
      @ ensures \result ==> referenceSet.orderedSetEquals(((OrderedSetComparator) obj).referenceSet);
      @ ensures !referenceSet.orderedSetEquals(((OrderedSetComparator) obj).referenceSet) ==> !\result;
      @*/
    public boolean equals(Object obj);
}
