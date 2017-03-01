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
import java.util.Set;

//@ import java.util.Iterator;

/**
 * @author marc
 *
 */
public interface ImmutIndexedSet<E> extends ImmutSet<E>, IndexedSet<E> {
    /**
     *  Returns a new ImmutSet which contains only the elements in this set that
     *  are contained in the specified set. In other words, construct the set
     *  obtained by removing from this set all of its elements that are not
     *  contained in the specified set. This operation return a new set whose value
     *  is the intersection of the two sets and may be used as an immutable version
     *  of the retainAll operation. The returned set is ordered
     * as this set. 
     *
     * @param  c  set that defines which elements the returned set will retain
     *      from this set.
     * @return       an ImmutSet which is the intersection of the two sets
     */
    /*@
      @ also
      @ requires c != null;
      @ ensures \result instanceof ImmutIndexedSet;
      @ ensures (\forall Object o1, o2; ((OrderedSet) \result).comparable(o1, o2);
      @                 comparable(o1, o2)
      @                 && (((OrderedSet) \result).lesserThan(o1, o2) <==> lesserThan(o1, o2)));
      @ ensures (\forall int i, j; i >= 0 && i < j && j < \result.size();
      @             lesserThan(((OrderedSet) \result).theList.itemAt(i), ((OrderedSet) \result).theList.itemAt(j)));
      @*/
    public Set<E> intersection(Collection<?> c);


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
    /*@
      @ also
      @ requires c != null;
      @ ensures \result instanceof ImmutIndexedSet;
      @ ensures (\forall Object o1, o2; ((OrderedSet) \result).comparable(o1, o2);
      @                 comparable(o1, o2)
      @                 ==> (((OrderedSet) \result).lesserThan(o1, o2) <==> lesserThan(o1, o2)));
      @ also
      @ old Iterator collecIter = c.iterator();
      @ requires c != null;
      @ ensures (\forall int i, j; i >= 0 && i < j && j < c.size();
      @                 (!comparable(collecIter.nthNextElement(i), collecIter.nthNextElement(j)) 
      @                  && ((collecIter.nthNextElement(i) != null && !collecIter.nthNextElement(i).equals(collecIter.nthNextElement(j)))
      @                      || (collecIter.nthNextElement(i) == null && collecIter.nthNextElement(j) != null)))
      @                 ==> ((OrderedSet) \result).lesserThan(collecIter.nthNextElement(i), collecIter.nthNextElement(j)));
      @*/
    public Set<E> union(Collection<? extends E> c);


    /**
     * Returns a new set that contains all the elements that are in 
     * this but not in the given argument. The returned set is ordered
     * as this set. 
     * 
     * @param c collection that defines which elements the returned set will 
     * not retain from this set.
     * @return a new set that represents the set difference of this with the 
     * specified collection of elements.
     */
    /*@
      @ also
      @ requires c != null;
      @ ensures \result instanceof ImmutIndexedSet;
      @ ensures (\forall Object o1, o2; ((OrderedSet) \result).comparable(o1, o2);
      @                 comparable(o1, o2)
      @                 && (((OrderedSet) \result).lesserThan(o1, o2) <==> lesserThan(o1, o2)));
      @ ensures (\forall int i, j; i >= 0 && i < j && j < \result.size();
      @             lesserThan(((OrderedSet) \result).theList.itemAt(i), ((OrderedSet) \result).theList.itemAt(j)));
      @*/
    public Set<E> difference(Collection<?> c);

}
