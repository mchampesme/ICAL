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

/**
 * @author Marc Champesme
 * @since 29 december 2005
 * @version 29 december 2005
 */
public class IndexedSetComparator<E> implements OrderedSetComparator<E> {
    //@ public represents referenceSet <- refIndexedSet;
    //@ public model instance IndexedSet refIndexedSet;
    //@ private represents refIndexedSet <- set;
    private IndexedSet<E> set;
    
    public IndexedSetComparator(IndexedSet<E> set) {
        this.set = set;
    }

    /**
     * @see orderedset.OrderedSetComparator#comparable(java.lang.Object, java.lang.Object)
     */
    public boolean comparable(E o1, E o2) {
        return (o1 == o2) || (set.contains(o1) && set.contains(o2));
    }

    /**
     * Compares two elements of this set for order. Returns a negative integer, zero, 
     * or a positive integer as the first argument is less than, equal to, or 
     * greater than the second.
     * 
     * @param o1 the first element of this set to be compared.
     * @param o2 the second element of this set to be compared.
     * @return a negative integer, zero, or a positive integer as the first 
     * argument is less than, equal to, or greater than the second.
     * 
     * @see orderedset.OrderedSetComparator#compare(java.lang.Object, java.lang.Object)
     * @throws ClassCastException - if the arguments are not contained in this set.
     */
    /*@ also
      @ requires o1 != null && o2 != null;
      @ requires referenceSet.contains(o1) && referenceSet.contains(o2); 
      @ ensures (\result < 0) <==> (refIndexedSet.indexOf(o1) < refIndexedSet.indexOf(o2));
      @ ensures (\result == 0) <==> (refIndexedSet.indexOf(o1) == refIndexedSet.indexOf(o2));
      @ ensures (\result > 0) <==> (refIndexedSet.indexOf(o1) > refIndexedSet.indexOf(o2));
      @*/
    public int compare(E o1, E o2) {
        if (o1 == o2) {
            return 0;
        }
        int index1 = set.indexOf(o1);
        int index2 = set.indexOf(o2);
        if (index1 == -1 || index2 == -1) {
            throw new ClassCastException();
        }
        return index1 - index2;
    }

}
