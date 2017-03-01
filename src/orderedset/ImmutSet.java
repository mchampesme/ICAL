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
 *  Immutable version of the set interface. All optional (modification)
 *  operations of the Set interface throw an UnsupportedOperationException and
 *  are replaced by equivalent operations which take a parameter of type Set and
 *  return a new set.
 *
 * @author     Marc Champesme
 * @version    22 décembre 2005
 * @since      15 december 2005
 */
public interface ImmutSet<E> extends ImmutSetOperations<E> {
	/*@
	  @ public represents nullElementsSupported <- false;
	  @ public represents addOperationSupported <- false;
	  @ public represents removeOperationSupported <- false;
	  @*/
	/**
	 *  Returns a new ImmutSet which contains only the elements in this set that
	 *  are contained in the specified set. In other words, construct the set
	 *  obtained by removing from this set all of its elements that are not
	 *  contained in the specified set. This operation return a new set whose value
	 *  is the intersection of the two sets and may be used as an immutable version
	 *  of the retainAll operation.
	 *
	 * @param  c  set that defines which elements the returned set will retain
	 *      from this set.
	 * @return       an ImmutSet which is the intersection of the two sets
	 */
	/*@
	  @ also
	  @ requires c != null;
	  @ ensures \result instanceof ImmutSet;
	  @*/
	public Set<E> intersection(Collection<?> c);


	/**
	 * @param  c
	 * @return
	 */
	/*@
	  @ also
	  @ requires c != null;
	  @ ensures \result instanceof ImmutSet;
	  @*/
	public Set<E> union(Collection<? extends E> c);


	/**
	 * @param  c
	 * @return
	 */
	/*@
	  @ also
	  @ requires c != null;
	  @ ensures \result instanceof ImmutSet;
	  @*/
	public Set<E> difference(Collection<?> c);


	/**
	 *  Unsupported operation.
	 *
	 * @param  o                               Description of the Parameter
	 * @return                                 Description of the Return Value
	 * @throws  UnsupportedOperationException  always.
	 * @see                                    java.util.Set#add(java.lang.Object)
	 */
	/*@ also
	  @ signals_only java.lang.UnsupportedOperationException;
	  @ signals (java.lang.UnsupportedOperationException) true;
	  @*/
	public boolean add(E o);


	/**
	 *  Unsupported operation.
	 *
	 * @param  o                               Description of the Parameter
	 * @return                                 Description of the Return Value
	 * @throws  UnsupportedOperationException  always.
	 * @see
	 *      java.util.Set#remove(java.lang.Object)
	 */
	/*@ also
	  @ signals_only java.lang.UnsupportedOperationException;
	  @ signals (java.lang.UnsupportedOperationException) true;
	  @*/
	public boolean remove(Object o);


	/**
	 *  Unsupported operation.
	 *
	 * @param  c                               The feature to be added to the All
	 *      attribute
	 * @return                                 Description of the Return Value
	 * @throws  UnsupportedOperationException  always.
	 * @see
	 *      java.util.Set#addAll(java.util.Collection)
	 */
	/*@ also
	  @ signals_only java.lang.UnsupportedOperationException;
	  @ signals (java.lang.UnsupportedOperationException) true;
	  @*/
	public boolean addAll(Collection<? extends E> c);


	/**
	 *  Unsupported operation.
	 *
	 * @param  c                               Description of the Parameter
	 * @return                                 Description of the Return Value
	 * @throws  UnsupportedOperationException  always.
	 * @see
	 *      java.util.Set#retainAll(java.util.Collection)
	 */
	/*@ also
	  @ signals_only java.lang.UnsupportedOperationException;
	  @ signals (java.lang.UnsupportedOperationException) true;
	  @*/
	public boolean retainAll(Collection<?> c);


	/**
	 *  Unsupported operation.
	 *
	 * @param  c                               Description of the Parameter
	 * @return                                 Description of the Return Value
	 * @throws  UnsupportedOperationException  always.
	 * @see
	 *      java.util.Set#removeAll(java.util.Collection)
	 */
	/*@ also
	  @ signals_only java.lang.UnsupportedOperationException;
	  @ signals (java.lang.UnsupportedOperationException) true;
	  @*/
	public boolean removeAll(Collection<?> c);


	/**
	 *  Unsupported operation.
	 *
	 * @throws  UnsupportedOperationException  always.
	 * @see                                    java.util.Set#clear()
	 */
	/*@ also
	  @ signals_only java.lang.UnsupportedOperationException;
	  @ signals (java.lang.UnsupportedOperationException) true;
	  @*/
	public void clear();
}

