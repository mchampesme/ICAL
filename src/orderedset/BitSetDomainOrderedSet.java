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

import java.util.AbstractSet;
import java.util.BitSet;
import java.util.Collection;
import java.util.Comparator;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.SortedSet;

//@ import org.jmlspecs.models.JMLEqualsSet;
//@ import org.jmlspecs.models.JMLType;
//@ import org.jmlspecs.models.JMLEqualsSequence;

/**
 * BitSet based implementation of a DomainOrderedSet.
 * 
 * @author     Marc Champesme
 * @since      15 december 2005
 * @version    29 décembre 2005
 */
public class BitSetDomainOrderedSet<E> extends AbstractSet<E> implements
	ImmutSetOperations<E>, DomainOrderedSet<E>,  SortedSet<E>,  Cloneable {
	/*@
      @ public invariant !domainContains(null);
	  @ public constraint domain() == \old(domain());
	  @ public represents addOperationSupported <- true;
	  @ public represents removeOperationSupported <- true;
      @ private represents theList <- JMLEqualsSequence.convertFrom(this);
      @*/
    /*@
	  @ private represents firstElement <- (JMLType) first();
	  @ private represents lastElement <- (JMLType) last();
	  @*/
	private ImmutIndexedSet<E> domain;
	private BitSet content;


	/**
     * Constructs a new, empty set with the specified domain.
	 * @param  domain the domain of this new set
	 */
	/*@
	  @ requires domain != null;
      @ requires !domain.contains(null);
      @ ensures isEmpty();
      @ ensures domain().equals(domain);
      @ ensures domain instanceof ImmutIndexedSet ==> domain() == domain;
      @ ensures domain instanceof IndexedSet 
      @     ==> (\forall int index; index >= 0 && index < domain.size();
      @             ((IndexedSet) domain()).get(index) == ((IndexedSet) domain).get(index));
	  @*/
	public BitSetDomainOrderedSet(Set<E> domain) {
        //@ set containsNull = false;
        //@ set elementType = \type(java.lang.Object);
        if (domain instanceof ImmutIndexedSet) {
            this.domain = (ImmutIndexedSet<E>) domain;
        } else {
            this.domain = new ArrayHashSet<E>(domain);
        }
		//content = new BitSet(domain.size());
        content = new BitSet();
	}

    /**
     * Constructs a new set with the specified domain containing 
     * the elements of the specified collection.
     * @param domain the domain of this new set
     * @param content a collection of elements from the specified 
     * domain to form the content of this new set
     */
    public BitSetDomainOrderedSet(Set<E> domain, Collection<? extends E> content) {
        this(domain);
        if (!content.isEmpty()) {
            if (content == domain) {
                this.content.set(0,domain.size());
            } else {
                addAll(content);
            }
        }
    }

    /**
     * @param  obj  Description of the Parameter
     * @return      The acceptableElement value
     * @see         orderedset.OrderedSet#isAcceptableElement(java.lang.Object)
     */
    public boolean isAcceptableElement(E obj) {
        return domainContains(obj);
    }


    public BitSetDomainOrderedSet<E> intersection(Collection<?> c) {
        if (c instanceof BitSetDomainOrderedSet) {
            BitSetDomainOrderedSet<?> set = (BitSetDomainOrderedSet<?>) c;
            return intersection(set);
        }
        BitSetDomainOrderedSet<E> resSet = (BitSetDomainOrderedSet<E>) clone();
        resSet.retainAll(c);
        return resSet;
    }

	/**
	 * @param  aSet
	 * @return
	 */
	/*@ 
	  @ requires aSet != null;
	  @ ensures \result instanceof BitSetDomainOrderedSet;
	  @ pure
	  @*/
	public BitSetDomainOrderedSet<E> intersection(BitSetDomainOrderedSet<?> aSet) {
		BitSetDomainOrderedSet<E> resSet = (BitSetDomainOrderedSet<E>) clone();
        if (sameDomainAs(aSet)) {
            BitSet newContent = resSet.content;
            newContent.and(aSet.content);
            resSet.content = newContent;
            return resSet;
        }
        resSet.retainAll(aSet);
        return resSet;
	}

    /* (non-Javadoc)
     * @see orderedset.ImmutSetOperations#union(java.util.Collection)
     */
    public BitSetDomainOrderedSet<E> union(Collection<? extends E> c) {
        if (c instanceof BitSetDomainOrderedSet) {
            BitSetDomainOrderedSet<? extends E> set = (BitSetDomainOrderedSet<? extends E>) c;
            return union(set);
        }
        BitSetDomainOrderedSet<E> resSet = (BitSetDomainOrderedSet<E>) clone();
        resSet.addAll(c);
        return resSet;
    }

	/**
	 * @param aSet
	 * @return
	 */
	public BitSetDomainOrderedSet<E> union(BitSetDomainOrderedSet<? extends E> aSet) {
		BitSetDomainOrderedSet<E> resSet = (BitSetDomainOrderedSet<E>) clone();
        if (sameDomainAs(aSet)) {
            BitSet newContent = resSet.content;
            newContent.or(aSet.content);
            resSet.content = newContent;
            return resSet;
        }
        resSet.addAll(aSet);
        return resSet;
	}

    /**
     * @param  c
     * @return
     * @see orderedset.ImmutSetOperations#difference(java.util.Set)
     */
    public BitSetDomainOrderedSet<E> difference(Collection<?> c) {
        if (c instanceof BitSetDomainOrderedSet) {
            BitSetDomainOrderedSet<?> set = (BitSetDomainOrderedSet<?>) c;
            return difference(set);
        }
        BitSetDomainOrderedSet<E> resSet = (BitSetDomainOrderedSet<E>) clone();
        resSet.removeAll(c);
        return resSet;
    }

	/**
	 * @param  aSet
	 * @return
	 */
	/*@
	  @ pure
	  @*/
	public BitSetDomainOrderedSet<E> difference(BitSetDomainOrderedSet<?> aSet) {
		BitSetDomainOrderedSet<E> resSet = (BitSetDomainOrderedSet<E>) clone();
        if (sameDomainAs(aSet)) {
            BitSet newContent = resSet.content;
            newContent.andNot(aSet.content);
            resSet.content = newContent;
        } else {
            resSet.removeAll(aSet);
        }
		return resSet;
	}


	/**
	 * @param  aSet  Description of the Parameter
	 * @return
	 */
	/*@
	  @ requires sameDomainAs(aSet);
	  @ pure
	  @*/
	public boolean intersects(BitSetDomainOrderedSet<E> aSet) {
		return content.intersects(aSet.content);
	}


	/**
	 *  Renvoie <code>true</code> si cet ensemble contient l'élément spécifié. Plus
	 *  précisément, renvoie <code>true</code> si et seulement si cette liste
	 *  contient un élément <code>e</code> tel que <code>elt.equals(e)</code>.
	 *
	 * @param  elt  L'élément dont on cherche &agrave; savoir s'il appartient
	 *      &agrave; cet ensemble.
	 * @return      <code>true</code> si l'élement spécifié est présent ; <code>false</code>
	 *      sinon.
	 */
	public boolean contains(Object elt) {
		int index = domain.indexOf(elt);
		if (index == -1) {
			return false;
		} else {
			return content.get(index);
		}
	}


	/**
	 *  Description of the Method
	 *
	 * @param  c  Description of the Parameter
	 * @return    Description of the Return Value
	 */
	public boolean containsAll(Collection<?> c) {
		if (c instanceof BitSetDomainOrderedSet) {
			BitSetDomainOrderedSet<?> set = (BitSetDomainOrderedSet<?>) c;
			if (sameDomainAs(set)) {
                BitSetDomainOrderedSet<?> diff = (BitSetDomainOrderedSet<?>) set.difference(this);
                return diff.isEmpty();
			}
		}
		return super.containsAll(c);
	}


	/**
	 *  Adds the specified element to this set if it is not already present. More
	 *  formally, adds the specified element, elt, to this set if the domain of
	 *  this set contains and this set contains no element e such that (o==null ?
	 *  e==null : o.equals(e)). If this set already contains the specified element,
	 *  the call leaves this set unchanged and returns false. In combination with
	 *  the restriction on constructors, this ensures that sets never contain
	 *  duplicate elements.
	 *
	 * @param  elt                        element to be added to this set.
	 * @return                            true if this set did not already contain
	 *      the specified element.
	 * @see                               java.util.AbstractCollection#add(java.lang.Object)
	 * @throws  NullPointerException      if the specified element is null.
	 * @throws  IllegalArgumentException  if the specified element is not in the
	 *      domain of this set.
	 */
	/*@ also
      @ signals (java.lang.NullPointerException) elt == null;
      @ signals (java.lang.IllegalArgumentException) !domainContains(elt);
      @*/
	public boolean add(E elt) {
		int index = domain.indexOf(elt);
		if (index != -1) {
			if (content.get(index)) {
				return false;
			} else {
				content.set(index);
				return true;
			}
            
		}
		throw new IllegalArgumentException();
	}

	public boolean addAll(Collection<? extends E> c) {
        if (c instanceof BitSetDomainOrderedSet) {
            BitSetDomainOrderedSet<? extends E> set = (BitSetDomainOrderedSet<? extends E>) c;
            if (sameDomainAs(set)) {
                int oldSize = size();
                fastAddAll(set);
                return size() > oldSize;
            }
        }
        return super.addAll(c);
    }
    
	/**
	 * @param  elt
	 */
	/*@
      @ requires elt != null;
      @ requires domainContains(elt);
      @ ensures contains(elt);
      @ also
      @ requires !this.domain().containsNull ==> elt != null;
      @ requires !domainContains(elt);
      @ assignable \nothing;
      @ ensures theSet.equals(\old(theSet));
      @*/
	public void fastAdd(E elt) {
		int index = domain.indexOf(elt);
		if (index != -1) {
			content.set(index);
		}
	}

    /**
     * @param set
     */
    /*@
      @ requires set != null;
      @ requires sameDomainAs(set);
      @ ensures theSet.equals(\old(theSet).union(set.theSet));
      @*/
    public void fastAddAll(BitSetDomainOrderedSet<? extends E> set) {
        content.or(set.content);
    }

	/**
	 *  Removes the specified element from this set if it is present. More
	 *  formally, removes an element e such that (o==null ? e==null : o.equals(e)),
	 *  if the set contains such an element. Returns true if the set contained the
	 *  specified element (or equivalently, if the set changed as a result of the
	 *  call). (The set will not contain the specified element once the call
	 *  returns.)
	 *
	 * @param  elt  object to be removed from this set, if present.
	 * @return      true if the set contained the specified element.
	 */
	public boolean remove(Object elt) {
		int index = domain.indexOf(elt);
		if ((index != -1) && content.get(index)) {
			content.clear(index);
			return true;
		}
		return false;
	}


	/**
	 * @param  elt
	 */
	/*@
      @ requires elt != null;
      @ ensures !contains(elt);
      @*/
	public void fastRemove(E elt) {
		int index = domain.indexOf(elt);
		if ((index != -1)) {
			content.clear(index);
		}
	}


	/**
	 *  Description of the Method
	 *
	 * @param  c  Description of the Parameter
	 * @return    Description of the Return Value
	 */
	public boolean removeAll(Collection<?> c) {
		if (c instanceof BitSetDomainOrderedSet) {
			BitSetDomainOrderedSet<?> set = (BitSetDomainOrderedSet<?>) c;
			if (sameDomainAs(set)) {
				int oldSize = size();
				content.andNot(set.content);
				return size() < oldSize;
			}
		}
		return super.removeAll(c);
	}


	/**
	 * @param  set
	 */
	/*@
      @ requires set != null;
      @ requires sameDomainAs(set);
      @ ensures this.theSet.equals(\old(this.theSet).difference(set.theSet));
      @*/
	public void fastRemoveAll(BitSetDomainOrderedSet<? extends E> set) {
		content.andNot(set.content);
	}


	/**
	 *  Description of the Method
	 *
	 * @param  c  Description of the Parameter
	 * @return    Description of the Return Value
	 */
	public boolean retainAll(Collection<?> c) {
		if (c instanceof BitSetDomainOrderedSet) {
			BitSetDomainOrderedSet<?> set = (BitSetDomainOrderedSet<?>) c;
			if (sameDomainAs(set)) {
				int oldSize = content.size();
				content.and(set.content);
				return size() != oldSize;
			}
		}
		return super.retainAll(c);
	}


    /**
     * @param set
     */
    /*@
      @ requires set != null;
      @ requires sameDomainAs(set);
      @ ensures theSet.equals(\old(theSet).intersection(set.theSet));
      @*/
    public void fastRetainAll(BitSetDomainOrderedSet<? extends E> set) {
        content.and(set.content);
    }
    
	/**
	 *  Enlève tous les éléments de cet ensemble.
	 */
	public void clear() {
		content.clear();
	}


	/**
	 *  Teste si cet ensemble ne contient aucun élément.
	 *
	 * @return    <code>true</code> si cet ensemble ne contient aucun élément ;
	 *      <code>false</code> sinon.
	 */
	public boolean isEmpty() {
		return content.isEmpty();
	}



	/**
	 *  Renvoie le nombre d'éléments dans cet ensemble.
	 *
	 * @return    le nombre d'éléments dans cet ensemble.
	 */
	public int size() {
		return content.cardinality();
	}


	/**
	 *  Renvoie une nouvelle instance de tableau contenant tous les éléments de cet
	 *  ensemble.
	 *
	 * @return    Un tableau contenant tous les éléments de cet ensemble.
	 */
	public Object[] toArray() {
		Object[] tab;
		tab = new Object[size()];
		for (int i = content.nextSetBit(0), j = 0; i >= 0;
			i = content.nextSetBit(i + 1), j++) {
			tab[j] = domain.get(i);
		}
		return tab;
	}

    public boolean orderedSetEquals(OrderedSet<?> set) {
        if (this == set) {
            return true;
        }
        if (size() != set.size()) {
            return false;
        }
        if (set instanceof BitSetDomainOrderedSet) {
            BitSetDomainOrderedSet<?> bSet = (BitSetDomainOrderedSet<?>) set;
            if (sameDomainAs(bSet)) {
                return content.equals(bSet.content);
            }
        }
        boolean allEquals = true;
        Iterator<E> thisIter = iterator();
        Iterator<?> otherIter = set.iterator();
        while (thisIter.hasNext() && allEquals) {
            allEquals = thisIter.next().equals(otherIter.next());
        }
        return allEquals;
    }


	/**
	 *  Teste l'égalité entre l'objet spécifié et cet ensemble. Renvoie <code>true</code>
	 *  si et seulement si l'objet spécifié est aussi un <code>Ensemble</code>, que
	 *  les deux ensembles ont le m&ecirc;me nombre d'éléments et que les deux
	 *  ensembles contiennent les m&ecirc;mes elements.
	 *
	 * @param  obj  l'objet &agrave; comparer avec cette liste.
	 * @return      <code>true</code> si l'objet spécifié est <i>equal </i>
	 *      &agrave; cette liste ; <code>false</code> sinon
	 */
	/*@
      @ also
      @ ensures !(obj instanceof Set && this.size() == ((Set)obj).size())
      @         ==> !\result;
      @ ensures (obj instanceof Set && this.size() == ((Set)obj).size())
      @     ==> (\result
      @         <==> (\forall Object o; contains(o);
      @                     ((Set)obj).contains(o))
      @              && (\forall Object o; ((Set)obj).contains(o);
      @                     contains(o)));
      @ pure
      @*/
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}

		if (!(obj instanceof Set)) {
			return false;
		}

		if (obj instanceof BitSetDomainOrderedSet) {
			BitSetDomainOrderedSet<?> bsEns = (BitSetDomainOrderedSet<?>) obj;
			return bsEns.domain.equals(this.domain)
				 && this.content.equals(bsEns.content);
		}

		Set<?> autreEnsemble = (Set<?>) obj;
		if (size() != autreEnsemble.size()) {
			return false;
		}

		return containsAll(autreEnsemble);
	}


	/**
	 *  Renvoie la valeur du code de hashage de cet ensemble. Le code de hashage
	 *  d'un ensemble est définit comme étant la somme des codes de hashage de ses
	 *  éléments. Ce calcul assure que <code>ens1.equals(ens2)</code> implique que
	 *  <code>ens1.hashCode()==ens2.hashCode()</code> pour toute paire d'ensembles,
	 *  <code>ens1</code> et <code>ens2</code>, comme le spécifie le contrat de
	 *  <code>Object.hashCode</code>.</p>
	 *
	 * @return    la valeur du code de hashage pour cet ensemble.
	 */
	//@ pure
	public int hashCode() {
		return domain.hashCode() + content.hashCode();
	}


	/**
	 * @return    Description of the Return Value
	 * @see       java.util.AbstractCollection#iterator() Description of the Method
	 */
	public Iterator<E> iterator() {
		return new BitSetDOSIterator<E>(domain, content, size());
	}


	/**
	 * @return    Description of the Return Value
	 * @see       orderedset.DomainOrderedSet#domain() Description of the Method
	 */
    /*@ also
      @ ensures \result instanceof ImmutIndexedSet;
      @*/
	public OrderedSet<E> domain() {
		return domain;
	}


	/**
	 * @param  o  Description of the Parameter
	 * @return    Description of the Return Value
	 * @see       orderedset.DomainOrderedSet#domainContains(java.lang.Object)
	 *      Description of the Method
	 */
	public boolean domainContains(Object o) {
		return domain.contains(o);
	}


	/**
	 *  Description of the Method
	 *
	 * @param  set  Description of the Parameter
	 * @return      Description of the Return Value
	 * @see         orderedset.DomainOrderedSet#sameDomainAs(orderedset.DomainOrderedSet)
	 */
	public boolean sameDomainAs(DomainOrderedSet<?> set) {
        if (domain == set.domain()) {
            return true;
        } else {
            return domain.orderedSetEquals(set.domain());
        }	
	}


	/**
	 * @return    Description of the Return Value
	 * @see       java.util.SortedSet#comparator() Description of the Method
	 */       
	public Comparator<? super E> comparator() {
		return domain.comparator();
	}


	/**
	 *  Description of the Method
	 *
	 * @param  arg0  Description of the Parameter
	 * @param  arg1  Description of the Parameter
	 * @return       Description of the Return Value
	 * @see          java.util.SortedSet#subSet(java.lang.Object, java.lang.Object)
	 */
	public SortedSet<E> subSet(E arg0, E arg1) {
		// TODO Auto-generated method stub
		return null;
	}


	/**
	 *  Returns a view of the portion of this sorted set whose elements are 
     *  strictly less than toElement. The returned sorted set is backed by this 
     *  sorted set, so changes in the returned sorted set are reflected in this 
     *  sorted set, and vice-versa. The returned sorted set supports all optional 
     *  set operations.
     *  
     *  The sorted set returned by this method will throw an IllegalArgumentException 
     *  if the user attempts to insert a element outside the specified range.
     *  
     *  Note: this method always returns a view that does not contain its (high) endpoint.
	 *
	 * @param  toElement  high endpoint (exclusive) of the headSet.
	 * @return       a view of the specified initial range of this sorted set.
	 * @see          java.util.SortedSet#headSet(java.lang.Object)
	 */
	public SortedSet<E> headSet(E toElement) {
		// TODO Auto-generated method stub
		return null;
	}


	/**
	 *  Description of the Method
	 *
	 * @param  arg0  Description of the Parameter
	 * @return       Description of the Return Value
	 * @see          java.util.SortedSet#tailSet(java.lang.Object)
	 */
	public SortedSet<E> tailSet(E arg0) {
		// TODO Auto-generated method stub
		return null;
	}


	/**
	 *  Returns the first (lowest) element currently in this sorted set.
	 *
	 * @return                          the first (lowest) element currently in
	 *      this sorted set.
	 * @see                             java.util.SortedSet#first()
	 * @throws  NoSuchElementException  - sorted set is empty.
	 */
	public E first() {
		int firstEltIndex = content.nextSetBit(0);
		if (firstEltIndex != -1) {
			return domain.get(firstEltIndex);
		}
		throw new NoSuchElementException();
	}


	/**
	 *  Returns the last (highest) element currently in this sorted set.
	 *
	 * @return                          the last (highest) element currently in
	 *      this sorted set.
	 * @see                             java.util.SortedSet#last()
	 * @throws  NoSuchElementException  - sorted set is empty.
	 */
	public E last() {
		if (isEmpty()) {
			throw new NoSuchElementException();
		}
		int lastIndex;
		boolean found = false;
		for (lastIndex = size() - 1; lastIndex >= 0 && !found; lastIndex--) {
			found = content.get(lastIndex);
		}
		if (found) {
			return domain.get(lastIndex);
		}
		return null;
	}


    /**
     * @return    Description of the Return Value
     * @see       java.lang.Object#clone()
     */
    /*@ also
      @ ensures orderedSetEquals((OrderedSet) \result);
      @ ensures ((DomainOrderedSet) \result).domain() == domain();
      @*/
    @SuppressWarnings("unchecked")
    public BitSetDomainOrderedSet<E> clone() {
        BitSetDomainOrderedSet<E> resSet;
        try {
            resSet = (BitSetDomainOrderedSet<E>) super.clone();
        } catch (CloneNotSupportedException e) {
            // Impossible
            throw new InternalError("Clone not supported" + e);
        }
        resSet.content = (BitSet) content.clone();
        return resSet;
    }

//    public String toString() {
//        return super.toString() + "@" + domain.toString();
//    }

}

