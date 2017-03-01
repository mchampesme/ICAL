/**
 * 
 */
package orderedset;

import java.util.Comparator;

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
/**
 * @author Marc Champesme
 * @since 15 december 2005
 *
 */
public interface DomainOrderedSet<E> extends OrderedSet<E> {
    /*@
      @ public invariant size() <= domain().size();
      @ public invariant (\forall Object o; ; isAcceptableElement(o) <==> domainContains(o));
      @ public invariant (\forall Object o; contains(o); domainContains(o));
      @ public invariant comparator().equals(domain().comparator());
      @ public represents nullElementsSupported <- domainContains(null);
      @*/
    
    /**
     * @see orderedset.OrderedSet#comparator()
     */
    /*@ also
      @ ensures \result.equals(domain().comparator());
      @*/
    public Comparator<? super E> comparator();
    
    /**
     * @return
     */
    /*@
      @ ensures \result != null;
      @ pure
      @*/
    public OrderedSet<E> domain();
    
    /**
     * @param o
     * @return
     */
    /*@
      @ ensures \result <==> domain().theSet.has(o);
      @ ensures (o == null && !this.containsNull) ==> !\result;
      @ pure
      @*/
    public boolean domainContains(Object o);
    
    /**
     * Returns true if the domain of the specified set contains the
     * same element in the same order than this set.
     * @param set the set whose domain is to be compared compared for equality 
     * with the domain of this set
     * @return true if the specified set has the same domain as this set.
     */
    /*@
      @ requires set != null;
      @ ensures \result <==> domain().orderedSetEquals(set.domain());
      @ pure
      @*/
    public boolean sameDomainAs(DomainOrderedSet<?> set);
    
    /**
     * @see orderedset.OrderedSet#isAcceptableElement(java.lang.Object)
     */
    /*@ also
      @ ensures \result <==> domainContains(o);
      @*/
    public boolean isAcceptableElement(E o);

}
