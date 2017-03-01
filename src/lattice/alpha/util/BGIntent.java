/*
 * **********************************************************************
 * Copyright (C) 2004 The Galicia Team Modifications to the initial code base
 * are copyright of their respective authors, or their employers as appropriate.
 * Authorship of the modifications may be determined from the ChangeLog placed
 * at the end of this file. This program is free software; you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of the
 * License, or (at your option) any later version. This program is distributed
 * in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even
 * the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details. You should have
 * received a copy of the GNU Lesser General Public License along with this
 * program; if not, write to the Free Software Foundation, Inc., 59 Temple
 * Place, Suite 330, Boston, MA 02111-1307 USA; or visit the following url:
 * http://www.gnu.org/copyleft/lesser.html
 * **********************************************************************
 */
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

package lattice.alpha.util;

import java.util.Collection;
import java.util.Comparator;
import java.util.SortedSet;
import java.util.TreeSet;

import lattice.util.concept.Intent;
import lattice.util.concept.FormalAttribute;

//@ import lattice.util.concept.FormalAttribute;
//@ model import org.jmlspecs.models.JMLEqualsSet;
/**
 * Better implementation of the Extent interface, main differences with respect
 * to SetExtent are: - addition of all the standard constructors for java
 * SortedSet - removal of the specific clone implementation
 * 
 * @author David Grosser (SetExtent implementation)
 * @author Marc Champesme
 * @version 1.0
 */
public class BGIntent extends TreeSet<FormalAttribute> implements Intent {
    /*@
      @ {
      @     set elementType = \type(FormalAttribute);
      @     set containsNull = false; 
      @ }
      @ public represents nullElementsSupported <- false;
      @ public represents addOperationSupported <- true;
      @ public represents removeOperationSupported <- true;
      @ private represents theSet <-  JMLEqualsSet.convertFrom(this);
      @ private represents firstElement <- (FormalAttribute) first();
      @ private represents lastElement <- (FormalAttribute) last();
      @*/
    
    /**
     * 
     */
    private static final long serialVersionUID = -1100186182458183112L;

    /**
     * Constructs a new, empty set, sorted according to the elements' natural order.
     */
    /*@
      @ ensures isEmpty();
      @ ensures this.theSet != null && this.theSet.isEmpty();
      @*/
    public BGIntent() {
        super();
    }

    /**
     * Constructs a new set containing the elements in the specified collection, 
     * sorted according to the elements' natural order. All keys inserted into 
     * the set must implement the Comparable  interface. Furthermore, all such 
     * keys must be mutually comparable: k1.compareTo(k2) must not throw a 
     * ClassCastException for any elements k1 and k2 in the set.
     * 
     * @param c The elements that will comprise the new set.
     */
    /*@
      @ public normal_behavior
      @     requires c != null;
      @     requires (\forall Object obj; c.contains(obj);
      @                             \typeof(obj) <: \type(FormalAttribute));
      @     assignable theSet;
      @     ensures theSet != null;
      @     ensures theSet.equals(JMLEqualsSet.convertFrom(c));
      @ also
      @ public exceptional_behavior
      @     requires c == null;
      @     assignable \nothing;
      @     signals (NullPointerException) c == null;
      @ also
      @ public exceptional_behavior
      @     requires !(\forall Object obj; c.contains(obj);
      @                             \typeof(obj) <: \type(FormalAttribute));
      @     assignable \nothing;
      @     signals (ClassCastException) (* the keys in the specified collection are not 
      @                                     instance of FormalAttribute. *);
      @*/
    public BGIntent(Collection<? extends FormalAttribute> c) {
        super(c);
    }
    
    /**
     * Constructs a new, empty set, sorted according to the specified 
     * comparator. All elements inserted into the set must be mutually 
     * comparable by the specified comparator: comparator.compare(e1, e2) 
     * must not throw a ClassCastException for any elements e1 and e2 in 
     * the set. If the user attempts to add an element to the set that 
     * violates this constraint, the add(Object) call will throw 
     * a ClassCastException.
     * 
     * @param c the comparator that will be used to sort this set. 
     * A null value indicates that the elements' natural 
     * ordering should be used.
     * 
     */
    /*@
      @ public normal_behavior
      @ assignable theSet;
      @ ensures this.theSet != null;
      @ ensures this.theSet.isEmpty();
      @ ensures cmp != null ==> comparator().equals(cmp);
      @ ensures cmp == null ==> comparator() == null;
      @*/
    public BGIntent(Comparator<? super FormalAttribute> cmp) {
        super(cmp);
    }
    
    /**
     * Constructs a new set containing the same elements as the 
     * specified sorted set, sorted according to the same ordering.
     * 
     * @param set     sorted set whose elements will comprise the new set. 
     */
    /*@
      @ public normal_behavior
      @     requires set != null;
      @     requires (\forall Object obj; set.contains(obj);
      @                             \typeof(obj) <: \type(FormalAttribute));
      @     assignable theSet;
      @     ensures theSet != null;
      @     ensures theSet.equals(set.theSet);
      @ also
      @ public exceptional_behavior
      @     requires set == null;
      @     assignable \nothing;
      @     signals (NullPointerException) set == null;
      @ also
      @ public exceptional_behavior
      @     requires !(\forall Object obj; set.contains(obj);
      @                             \typeof(obj) <: \type(FormalAttribute));
      @     assignable \nothing;
      @     signals (ClassCastException) (* the keys in the specified collection are not 
      @                                     instance of FormalAttribute. *);
      @*/
    public BGIntent(SortedSet<? extends FormalAttribute> set) {
        super(set);
    }
    
    /**
     * Immutable version of the addAll method.
     * @param intent elements to be added to this set
     * @return result A new instance which contains all elements of this and the specified Intent 
     */
    /*@ also
      @ requires intent != null;
      @ ensures \fresh(\result);
      @ ensures \result.theSet.equals(this.theSet.union(intent.theSet)); 
      @ pure
      @*/
    public Intent intentUnion(Intent intent) {
        Intent result = (Intent) this.clone();
        result.addAll(intent);
        return result;
    }

    /**
     * Immutable version of the retainAll method.
     * @param intent
     * @return result
     */
    /*@ also
      @ requires intent != null;
      @ ensures \fresh(\result);
      @ ensures \result.theSet.equals(this.theSet.intersection(intent.theSet)); 
      @ pure
      @*/
    public Intent intentIntersection(Intent intent) {
        Intent result = (Intent) this.clone();
        result.retainAll(intent);
        return result;
    }
    
    public BGIntent clone() {
        return (BGIntent) super.clone();
    }
}
