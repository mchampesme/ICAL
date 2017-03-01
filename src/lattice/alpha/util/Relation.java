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
import java.util.Iterator;

import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.structure.CompleteConceptLattice;

public interface Relation extends Iterable<Couple<FormalObject, FormalAttribute>> {

    public final static String DEFAULT_NAME = "Default Name";

    public String getName();
    
    public void setName(String newName);

    public CompleteConceptLattice getLattice();
    
    public void setLattice(CompleteConceptLattice lattice);

    public boolean contains(FormalObject Obj, FormalAttribute Att);

    public boolean contains(FormalAttribute fa);

    public boolean contains(FormalObject fo);
    
    public Iterator<Couple<FormalObject, FormalAttribute>> iterator();

    public Iterator<FormalObject> objectIterator();
    
    public Iterator<FormalAttribute> attributeIterator();
    
    /**
     * Returns an unmodifiable view of the list of FormalObject of this relation.
     * 
     * @return an unmodifiable view of the list of FormalObject of this relation.
     */
    public Collection<FormalObject> getObjects();
    
    /**
     * Returns an unmodifiable view of the list of FormalAttribute of this relation.
     * 
     * @return an unmodifiable view of the list of FormalAttribute of this relation.
     */
    public Collection<FormalAttribute> getAttributes();
    
    /**
     * @param fa
     * @return
     */
    public Extent getExtent(FormalAttribute fa);
    
    /**
     * @param fo
     * @return
     */
    public Intent getIntent(FormalObject fo);
    
    /**
     * @return
     */
    public int getObjectsNumber();

    public int getAttributesNumber();

    public int size();
}