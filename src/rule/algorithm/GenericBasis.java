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

// import java
import java.util.Iterator;

import lattice.alpha.util.BGIntent;
import lattice.util.concept.Concept;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.Node;
import rule.util.Rule;

/**
 * @author leflocha
 * @author Marc Champesme (generic version)
 *
 */


/*******************************************************************************************/
/* Cette classe permet de g�n�rer la base g�n�rique de Pasquier (r�gles exactes)           */
/* a partir des concepts fr�quents et de ses g�n�rateurs associ�s. Les g�n�rateurs ont �t� */
/* pr�alablement construits par l'algorithme JEN.                                          */
/* R�gle : g�n�rateur --> ConceptFr�quent \ g�n�rateur                                     */
/* confiance = 1.0                                                                         */
/* support = support(ConceptFrequent)                                                      */
/*******************************************************************************************/


public class GenericBasis extends AbstractRuleAlgorithm {

// CONSTRUCTEUR
  public GenericBasis(CompleteConceptLattice treillis, double minConfiance) {
  	super(treillis, minConfiance, 1.0);
  }


  // M�THODES D'INSTANCE
  // Cette m�thode permet d'obtenir la cons�quence r�duite des r�gles.
  // r�gle: ant�c�dent --> consequenceNonReduite \ ant�c�dent
  // consequenceReduit = consequenceNonReduite \ ant�c�dent
  public Intent reductionConsequence( Intent consequenceNonReduite, Intent antecedent ) {
	  Intent consequenceReduit = new BGIntent();

     // Parcours de tous les items de la cons�quence non r�duite de la r�gle
    Iterator<FormalAttribute> it = consequenceNonReduite.iterator();
    while ( it.hasNext() ) {

      // Pour chaque item
    	FormalAttribute item = it.next();

      // Si celui-ci n'est pas inclus dans l'ant�c�dent
      if ( !antecedent.contains( item ) ) {

        // Alors il fait n�cessairement partie de la cons�quence r�duite
        consequenceReduit.add( item );
      }
    }
    return consequenceReduit;
  }

/**************************************************************/
/* Ensemble de r�gles obtenues a patir d'un noeud du treillis */
/**************************************************************/

  // G�n�ration de l'ensemble des r�gles g�n�r�es a partir du fci rentr� en param�tre
  public void generationbaseGeneriqueNoeud( Node<Concept> noeudTreillis, float nombreObjets  ) {
	
    
  	if ( noeudTreillis.getContent().getIntent().size() > 1 ) {
    	
    	// Parcours des g�n�rateurs du concept courant
    	Iterator<Intent> generateurNoeud = noeudTreillis.getContent().getGenerator().iterator();
      	while ( generateurNoeud.hasNext() ) {
        
        	// S�lectio du g�n�rateur courant
        	Intent generateurCourant = generateurNoeud.next();
        		 
        	double supportRegle = ((double)noeudTreillis.getContent().getExtent().size()) / nombreObjets;
        
        	// Calcul de la cons�quence de la r�gle potentielle
        	Intent consequencePotentielle = this.reductionConsequence( noeudTreillis.getContent().getIntent(), generateurCourant );
       
       		
        	if ( consequencePotentielle.size()!= 0 ) {
        		
        		// Conservation de la r�gle
          		Rule nouvelleRegle = new Rule ( generateurCourant, consequencePotentielle, supportRegle, 1.0 );
          		
          		// Insertion dans l'ensemble des r�gles de la base g�n�rique
          		this.getBase().add(nouvelleRegle);
			}
		}
	}
  }

/******************/
/* Base G�n�rique */
/******************/

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
      this.generationbaseGeneriqueNoeud( noeudCourant, (float)nombreObjets );
      
      // Gestion du poucentage de travail
	  numNodeCurrent++;
      sendJobPercentage((numNodeCurrent*100)/nbMaxNode);
    }
	getStringResult().append(getBase().toString()+"\n");
    //console.addMessage("End "+getDescription()+"\n");
  }

	public String getDescription() {
		return new String("Generic basis");
	}

/*  public String toString() {
  	return baseGenerique.toString();
  	String s = "Nombre de r?gles : " +baseGenerique.size()+"\n";
  	for(Iterator it = baseGenerique.iterator(); it.hasNext(); ) {
          Regle regleCourante = (Regle)it.next();
          s += regleCourante.toString();
        } 		

  	return s
  }*/



	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		doAlgorithm();
		if(jobObserv!=null) jobObserv.jobEnd(true);
	}

}
