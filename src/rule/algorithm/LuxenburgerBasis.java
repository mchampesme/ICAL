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

/************************************************************************/
/* Cette classe permet de g�n�rer l'ensemble des r�gles approximatives  */
/* de la base de couverture de Luxemburger.                             */
/************************************************************************/

/**
 * @author leflocha
 */

import java.util.Iterator;
import java.util.List;
import java.util.Set;

import lattice.alpha.util.BGIntent;
import lattice.util.concept.Concept;
import lattice.util.concept.Intent;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.Node;
import rule.util.Rule;

public class LuxenburgerBasis extends AbstractRuleAlgorithm {

  // CONSTRUCTEUR

  public LuxenburgerBasis(CompleteConceptLattice treillis, double minConfiance, double minSupport) {
	super(treillis, minConfiance, minSupport);
  }


  // METHODES D'INSTANCE

  // Cette m�thode permet d'obtenir la cons�quence r�duite des r�gles.
  // r�gle: ant�c�dent --> consequenceNonReduite \ ant�c�dent
  // consequenceReduit = consequenceNonReduite \ ant�c�dent
  
  public Intent reductionConsequence(Intent consequenceNonReduite,
			Intent antecedent) {
		Intent consequenceReduit = new BGIntent(consequenceNonReduite);
		consequenceReduit.removeAll(antecedent);
		return consequenceReduit;
	}

	/**
	 * Ensemble de règles obtenues a partir d'un noeud du treillis Génération de
	 * la base de couverture de Luxemburger à partir d'un concept fréquent
	 * 
	 * @param noeudTreillis
	 * @param nombreObjets
	 * @return
	 */
	public Set<Rule> generationBaseCouvertureNoeud(Node<Concept> noeudTreillis,
			float nombreObjets) {

		// Détermination de l'ensemble des concepts enfants du concept courant
		List<Node<Concept>> predecesseursImmediats = noeudTreillis
				.getChildren();

		if ((predecesseursImmediats.size() != 0)
				&& (noeudTreillis.getContent().getIntent().size() != 0)) {

			// Support de l'antécédant de la règle
			float supportAntecedent = ((float) noeudTreillis.getContent()
					.getExtent().size())
					/ nombreObjets;

			// Parcours des antécédents potentiels
			Iterator<Node<Concept>> it1 = predecesseursImmediats.iterator();
			while (it1.hasNext()) {

				// Pour chaque antécédent
				Node<Concept> consequenceRegle = it1.next();

				// Support de la conséquence potentielle de la règle
				float supportConsequence = ((float) consequenceRegle
						.getContent().getExtent().size())
						/ nombreObjets;

				// Calcul de la confiance de la règle candidate
				double confianceRegle = supportConsequence / supportAntecedent;

				// Si cette dernière est supérieure ou égale a la confiance
				// minimale
				if (confianceRegle >= this.getMinConfiance()) {

					// Conservation de la règle
					Rule nouvelleRegle = new Rule(noeudTreillis.getContent()
							.getIntent(), this.reductionConsequence(
							consequenceRegle.getContent().getIntent(),
							noeudTreillis.getContent().getIntent()),
							supportConsequence, confianceRegle);

					// Insertion dans l'ensemble des règles de la base de
					// couverture
					this.getBase().add(nouvelleRegle);
				}
			}
		}

		return getBase();
	}

/** 
* Base de luxemburger:  Génération de la base de couverture de Luxemburger de 
* l'ensemble des concepts fréquents
*/
  public void doAlgorithm() {
  	super.doAlgorithm();

  	// Nombre d'objets du contexte
	int nombreObjets = getLattice().getTop().getContent().getExtent().size();
    
	int nbMaxNode=getLattice().size();
	int numNodeCurrent=0;
        
    
    // Parcours de l'ensemble des concepts fréquents
    Iterator<Node<Concept>> it1 = this.getLattice().iterator();
    
    while ( it1.hasNext() ) {

      // Sélection du concept fréquent courant
    	Node<Concept> noeudCourant = it1.next();
      
      // G�n�ration des r�gles a partir de ce concept
      this.generationBaseCouvertureNoeud( noeudCourant, (float) nombreObjets );
      
	  numNodeCurrent++;
	  sendJobPercentage((numNodeCurrent*100)/nbMaxNode);

    }
	getStringResult().append(getBase().toString()+"\n");
	//console.addMessage("End "+getDescription()+"\n");
  }

	public String getDescription() {
		return new String("Luxenburger Basis");
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		doAlgorithm();
		if(jobObserv!=null) jobObserv.jobEnd(true);
	}
  
}









