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

package rule.algorithm;

import java.util.Iterator;
import java.util.List;

import lattice.alpha.util.BGIntent;
import lattice.util.concept.Concept;
import lattice.util.concept.Intent;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.Node;
import rule.util.Rule;


/**
 * @author leflocha
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */

public class InformativeBasis extends AbstractRuleAlgorithm {

  // CONSTRUCTEUR

  public InformativeBasis(CompleteConceptLattice treillis, double minConfiance) {
    super(treillis, minConfiance, 1.0);
  }


  // METHODES D'INSTANCE

  // Cette m�thode permet d'obtenir la cons�quence r�duite des r�gles.
  // r�gle: ant�c�dent --> consequenceNonReduite \ ant�c�dent
  // consequenceReduit = consequenceNonReduite \ ant�c�dent
  public Intent reductionConsequence( Intent consequenceNonReduite, Intent antecedent ) {
	  Intent consequenceReduit = new BGIntent(consequenceNonReduite);
	  consequenceReduit.removeAll(antecedent);
	  return consequenceReduit;
  }

/**************************************************************/
/* Ensemble de r�gles obtenues a partir d'un noeud du treillis */
/**************************************************************/

  	// G�n�ration de l'ensemble des r�gles g�n�r�es a partir du concept courant
	public void generationRegleNoeud( Node<Concept> noeudTreillis, float nombreObjets   ) {
  	
		// Parcours des g�n�rateurs du concept courant
		float supportAntecedent = ((float)noeudTreillis.getContent().getExtent().size())/ nombreObjets;
      	Iterator<Intent> generateurNoeud = noeudTreillis.getContent().getGenerator().iterator();
      	while ( generateurNoeud.hasNext() ) {
       		
       		// S�lection du g�n�rateur courant
       		Intent generateurCourant = generateurNoeud.next();
        
       		List<Node<Concept>> predecesseursImmediats =  noeudTreillis.getChildren();
       		if (!predecesseursImmediats.isEmpty()
					&& !noeudTreillis.getContent().getIntent().isEmpty()) {
        
        		// Parcours des concepts enfants du concept courant
        		Iterator<Node<Concept>> it1 = predecesseursImmediats.iterator();
      			while ( it1.hasNext() ) {
      		
      				// S�lection du concept enfant courant
      				Node<Concept> pred = it1.next();
          
          			float supportConsequence = ((float)pred.getContent().getExtent().size()) / nombreObjets;
          			
          			// Calcul de la cons�quence de la r�gle potentielle
          			Intent consequencePotentielle = this.reductionConsequence( pred.getContent().getIntent(), generateurCourant );
          			
          			// Calcul de la confiance de la r�gle candidate
          			double confianceRegle = supportConsequence  / supportAntecedent;
        
        			// Si cette derni�re est sup�rieure ou �gale a la confiance minimale
          			if ((consequencePotentielle.size() != 0)
							&& (confianceRegle >= this.getMinConfiance())) {
            			
            			// Conservation de la r�gle
            			Rule nouvelleRegle = new Rule ( generateurCourant, consequencePotentielle, supportConsequence, confianceRegle );
            			
            			// Insertion dans l'ensemble des r�gles de la base informative
            			getBase().add ( nouvelleRegle );
          			}
        		}
      		}
     	}
  	}

/********************/
/* Base Informative */
/********************/

  // G�n�ration de l'ensemble des r�gles de la base g�n�rique
  public void doAlgorithm() {
  	super.doAlgorithm();
  	// Nombre d'objets du contexte
    int nombreObjets = getLattice().getTop().getContent().getExtent().size();
    
	int nbMaxNode=getLattice().size();
	int numNodeCurrent=0;
    
    // Parcours de l'ensemble des concepts courants
    Iterator<Node<Concept>> it1 = this.getLattice().iterator();
    
    while ( it1.hasNext() ) {
    	
    	// S�lection du concept fr�quent courant
    	Node<Concept> noeudCourant = it1.next();
    	
    	// G�n�ration des r�gles a partir de ce concept
    	this.generationRegleNoeud( noeudCourant, (float)nombreObjets );

		numNodeCurrent++;
		sendJobPercentage((numNodeCurrent*100)/nbMaxNode);
    }
	getStringResult().append(getBase().toString()+"\n");
    //console.addMessage("End "+getDescription()+"\n");
  }
  
  public String getDescription() {
  	return new String("Informative basis");
  }

/* (non-Javadoc)
 * @see java.lang.Runnable#run()
 */
public void run() {
	doAlgorithm();
	if(jobObserv!=null) jobObserv.jobEnd(true);
}

}
