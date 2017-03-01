/*
 ***********************************************************************
 * Copyright (C) 2004 The Galicia Team 
 *
 * Modifications to the initial code base are copyright of their
 * respective authors, or their employers as appropriate.  Authorship
 * of the modifications may be determined from the ChangeLog placed at
 * the end of this file.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
 * USA; or visit the following url:
 * http://www.gnu.org/copyleft/lesser.html
 *
 ***********************************************************************
 */


package lattice.util.structure;

import lattice.util.concept.ConceptImp;



/**
 * Title:
 * Description: Structure d'un noeud pour l'algo Nourine & Reynaud
 * Copyright:    Copyright (c) 2001
 * Company: Université de Montréal
 * @author Dmitry Pestov
 * @version 1.0
 */

public class LatticeNodeNR extends ConceptNodeImp
{
    private int compteur;
    
    /**
     * CONSTRUCTEUR1
     * @param concept
     */
    public LatticeNodeNR(ConceptImp concept)
    {
	super(concept);
	compteur = 0;
    }
    
    /**
     * CONSTRUCTEUR2
     * Ce constructeur est appelé lors de la reconstitution du treillis.
     * @param id
     * @param concept
     */
    
    public LatticeNodeNR(Integer id, ConceptImp concept)
    {
	super(id, concept);
	compteur = 0;
    }
    
    /**
     * Attribuer une valeur au compteur
     * @param c
     */
    public void setCompteur(int c)
    {
	compteur = c;
    }
    
    /**
     * Icrémenter le compteur
     * 
     */
    public void incCompteur()
    {
	compteur++;
    }
    
    /**
     * retourne la valeur du compteur
     * @return compteur
     */
    public int getCompteur()
    {
	return compteur;
    }
} // fin classe
