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

package rule.util;



/********************************************************************************/
/* Cette classe permet d'effectuer la différence d'attributs entre deux intents.*/                      
/********************************************************************************/

/**
 * @author leflocha
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
import java.util.Iterator;

import lattice.util.concept.Concept;
import lattice.util.concept.Intent;
import lattice.util.concept.SetIntent;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.Node;

public class IntentDifference {

  // VARIABLES D'INSTANCE

  public Intent difference; // difference entre deux intents


  // CONSTRUCTEUR

  public IntentDifference() {
    this.difference = new SetIntent();
  }

  // METHODES D'INSTANCE

  public void calculDifference( Node<Concept> fci, Node<Concept> parentCourant ) {
    this.difference = this.ajouteNoeud( fci );
    this.difference.removeAll( parentCourant.getContent().getIntent() );
  }

   public Intent ajouteNoeud( Node<Concept> fci ) {
    Intent resultat = new SetIntent();
    resultat.addAll(fci.getContent().getIntent());
    return resultat;
  }
}


