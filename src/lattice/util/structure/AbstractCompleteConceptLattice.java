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

package lattice.util.structure;

import lattice.util.concept.Concept;
import lattice.util.relation.RelationBuilder;

/**
 * <p>
 * Title: Classe abstraite des treillis
 * </p>
 * <p>
 * Description: Implémente le squelette des AbstractCompleteConceptLattice
 * </p>
 * <p>
 * Copyright: Copyright (c) 2002
 * </p>
 * <p>
 * Company:
 * </p>
 * 
 * @author David Grosser
 * @version 1.0
 */

/*
 * Title : Réingénierie du package util : Fusion de util et util2 Description :
 * Fusion de la classe AbstractConceptLattice (util) et de la classe
 * CompleteConceptLattice (util2) Copyright: Copyright (c) 2004 Company:
 * Universite de Montréal
 * 
 * @author Mame Awa Diop et Petko Valtchev 
 * @version 1.1 
 */

// Fusion util util2 : ajout de : extends ConceptualSupSemiLattice
// implements CompleteLattice , ConceptNode

public abstract class AbstractCompleteConceptLattice implements
        CompleteConceptLattice {
    String description = "No Description";

    protected RelationBuilder binRel;

    protected Node<Concept> top;

    protected Node<Concept> bottom;

    /**
     *
     */
    public AbstractCompleteConceptLattice() {
    }

    // -------------------------------------------------------
    // Fusion de util util2 : ajout d'un nouveau constructeur
    // correspondant a AbstractCompleteConceptLattice (util2)
    // ajout de la variable bottom

    /** * Constructor for AbstractCompleteConceptLattice. */
    public AbstractCompleteConceptLattice(RelationBuilder relation) {
        binRel = relation;
        bottom = null;
        top = null;
    }

    // --------------------------------------------------------

    // -------------------------------------------------------
    // Fusion de util util2 : ajout des methodes de CompleteConceptLattice
    // (util2)

    public Node<Concept> getTop() {
        return top;
    }


    /**
     * @see lattice.util.structure.InfSemiLattice#getBottom()
     */
    public Node<Concept> getBottom() {
        return (Node<Concept>) bottom;
    }

    /**
     * @see lattice.util.structure.InfSemiLattice#setBottom(Comparable)
     */
    public void setBottom(Node<Concept> bottom) {
        // ---------------------------------------------------------
        // Modification a cause de fusion util et util2
        this.bottom = (Node<Concept>) bottom;
    }

    /**
     * @see lattice.util.structure.SupSemiLattice#setTop(Comparable)
     */
    public void setTop(Node<Concept> top) {
        // ----------------------------------------------------
        // Modification a cause de fusion util et util2

        this.top = (Node<Concept>) top;
    }


    // ------------------------------------------------------

    public String getDescription() {
        return description;
    }

    public void setDescription(String aDesc) {
        description = aDesc;
    }

    public String toString() {
        if (binRel != null)
            return binRel.getName() + "" + getDescription();
        else
            return getDescription();

    }

    public boolean equals(Object o) {
        if (o instanceof AbstractCompleteConceptLattice) {
            AbstractCompleteConceptLattice abs = (AbstractCompleteConceptLattice) o;
            return (abs.toString().equals(this.toString()));

        } else
            return false;
    }

}
