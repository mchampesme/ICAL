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

import java.util.Collections;
import java.util.List;

import lattice.util.concept.Concept;
import lattice.util.concept.Extent;
import lattice.util.concept.Intent;

/**
 * Better implementation of the Concept interface, main differences with respect
 * to ConceptImp are: - correct implementation of hashCode - obsoletes
 * operations getSimplifyExtent and getSimplifyEIntent throw an
 * UnsupportedOperationException.
 * 
 * @author Mame Awa Diop et Petko Valtchev (for ConceptImp implementation)
 * @author Marc Champesme (for this implementation)
 * @version 1.0
 */

public class BGConcept implements Concept {
    private Extent extent;

    private Intent intent;

    private List<Intent> generator;

    private int hashCodeValue;

    /**
     * @param extent
     * @param intent
     */
    public BGConcept(Extent extent, Intent intent) {
        this.extent = extent;
        this.intent = intent;
        this.generator = Collections.emptyList();
        computeHashCode();
    }

    /**
     * @return extent
     */
    public Extent getExtent() {
        return extent;
    }

    /**
     * @return intent
     */

    public Intent getIntent() {
        return intent;
    }

    /**
     * @return generator
     */

    public List<Intent> getGenerator() {
        return generator;
    }



    /**
     * @param extent
     */
    public void setExtent(Extent extent) {
        this.extent = extent;
        computeHashCode();
    }

    /**
     * @param generator
     */
    public void setGenerator(List<Intent> generatorsList) {
        this.generator = generatorsList;
    }

    /**
     * @param intent
     */
    public void setIntent(Intent intent) {
        this.intent = intent;
        computeHashCode();
    }

    /**
     * Deux concepts sont �gaux si leurs intents et extents sont �gaux.
     * 
     * @param obj
     * @return boolean value
     */
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (!(obj instanceof Concept)) {
            return false;
        }
        Concept concept_out = (Concept) obj;
        return extent.equals(concept_out.getExtent())
               && intent.equals(concept_out.getIntent());
    }

    public void computeHashCode() {
        hashCodeValue = (extent.hashCode() * 31) + intent.hashCode();
    }

    public int hashCode() {
        return hashCodeValue;
    }

    /**
     * affiche le contenu de l'extent et l'intent d'un concept.
     * 
     * @return
     */
    public String toString() {
        String string = "";
        string = string.concat("{ ");
        string = string.concat(extent.toString());
        string = string.concat(" , ");
        string = string.concat(intent.toString());
        string = string.concat(" }");
        return string;
    }

}
