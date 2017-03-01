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

//@ import org.jmlspecs.models.JMLEqualsSet;

/**
 * Extension of the set interface with the usual set operations defined in such 
 * a way that these operations can be performed without modification of the
 * current instance (they take a parameter of type Set and return a new set).
 * 
 * @author Marc Champesme
 * @since 15 december 2005
 */
public interface ImmutSetOperations<E> extends Set<E> {
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
     */
    /*@
      @ public behavior
      @ requires c != null;
      @ ensures \result.theSet.equals(this.theSet.intersection(org.jmlspecs.models.JMLEqualsSet.convertFrom(c)));
      @ ensures \result.size() <= Math.min(this.size(), c.size());
      @ signals_only java.lang.ClassCastException, java.lang.NullPointerException;
      @ signals (java.lang.ClassCastException) (* the type of one or more of the elements in c is not supported by this *);
      @ signals (java.lang.NullPointerException) (* argument contains null elements and this does not support null elements *);
      @ also
      @ public exceptional_behavior
      @     requires c == null;
      @     assignable \nothing;
      @     signals_only java.lang.NullPointerException;
      @
      @ pure
      @*/
    public Set<E> intersection(Collection<?> c);
    
    /**
     * Returns a new set that contains all the elements that 
     * are in either this or the given argument.
     * @param c collection that defines which elements the returned set will contain 
     * in addition to the elements of this set.
     * @return a Set which is the union of the two sets
     */
    /*@
      @ public behavior
      @ requires c != null;
      @ assignable \nothing;
      @ ensures \result.theSet.equals(this.theSet.union(org.jmlspecs.models.JMLEqualsSet.convertFrom(c)));
      @ ensures \result.size() <= this.size() + c.size();
      @ signals_only java.lang.IllegalArgumentException, java.lang.ClassCastException, java.lang.NullPointerException;
      @ signals (java.lang.ClassCastException) (* the type of one or more of the elements in c is not supported by this *);
      @ signals (java.lang.NullPointerException) (* argument contains null elements and this does not support null elements *);
      @ also
      @ public exceptional_behavior
      @     requires c == null;
      @     assignable \nothing;
      @     signals_only java.lang.NullPointerException;
      @ pure
      @*/
    public Set<E> union(Collection<? extends E> c);
    
    /**
     * Returns a new set that contains all the elements that are in 
     * this but not in the given argument.
     * 
     * @param c collection that defines which elements the returned set will 
     * not retain from this set.
     * @return a new set that represents the set difference of this with the 
     * specified collection of elements.
     */
    /*@
    @ public behavior
    @ requires c != null;
    @ ensures \result.theSet.equals(this.theSet.difference(org.jmlspecs.models.JMLEqualsSet.convertFrom(c)));
    @ ensures \result.size() <= this.size();
    @ signals_only java.lang.ClassCastException, java.lang.NullPointerException;
    @ signals (java.lang.ClassCastException) (* the type of one or more of the elements in c is not supported by this *);
    @ signals (java.lang.NullPointerException) (* argument contains null elements and this does not support null elements *);
    @ also
    @ public exceptional_behavior
    @     requires c == null;
    @     assignable \nothing;
    @     signals_only java.lang.NullPointerException;
    @
    @ pure
    @*/
    public Set<E> difference(Collection<?> c);

}
