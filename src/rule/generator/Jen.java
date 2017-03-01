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

package rule.generator;

/************************************************************************************/
/* Cette classe permet de construre l'ensemble des g�n�rateurs associ�s a un noeud. */
/************************************************************************************/

/**
 * @author leflocha
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */


import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Vector;

import lattice.gui.tooltask.AbstractJob;
import rule.util.IntentDifference;
import lattice.util.concept.Concept;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import lattice.util.concept.SetIntent;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.Node;

public class Jen extends AbstractJob {


  // VARIABLES D'INSTANCE

  
  public int nombreGenerateurs; // nombre de g�n�rateurs (totaux (pour l'ensemble du treillis))
  public IntentDifference dif;
  public CompleteConceptLattice instanceTreillis; // ensemble des concepts fr�quents du treillis

  // CONSTRUCTEUR

  public Jen (CompleteConceptLattice treillis) {
    this.dif = new IntentDifference();
    this.nombreGenerateurs = 0;
    this.instanceTreillis = treillis;
  }

  // METHODES D'INSTANCE

  // Retourne les diff�rets attributs d'un intent
  public Vector retourneItemItemset ( Intent itemset ) {
    Vector resultat = new Vector();
    for (FormalAttribute courant : itemset) {
      Intent tempo = new SetIntent();
      tempo.add( courant );
      resultat.add( tempo );
    }
    return resultat;
  }

  // Retourne la premi�re face de l'enesmble des faces d'un noeud
  public Intent retournePremierFace ( Vector ensembleFace ) {
    Iterator it = ensembleFace.iterator();
    Intent premiereFace = (Intent)it.next();
    return premiereFace;
  }

  // Calcul les faces d'un noeud
  public Vector calculFace( Node<Concept> fci ) {
    Vector ensembleFaces = new Vector();
    Set parents = fci.getParents();
    Iterator it = parents.iterator();
    while ( it.hasNext() ) {
        Node<Concept> parentCourant = (Node<Concept>)it.next();
      	dif.calculDifference( fci, parentCourant );
      	ensembleFaces.add( dif.difference );
    }
    return ensembleFaces;
  }

  // Retourne l'intersection entre un g�n�rateur et une face
  public Intent intersectionGenerateurFaceVide( Intent generateur, Intent face ) {
    Intent inter = generateur.intentIntersection( face );
    if ( inter.size()== 0 ) {
      return new SetIntent();
    } else {
      return inter;
    }
  }

  // Retourne un nouveau g�n�rateur form� de l'union d'un ancien g�n�rateur et d'une face
  public Intent calculNouveauGenerateur( Intent generateur, Intent face ) {
    Intent union = generateur.intentUnion( face );
    return union;
  }


  // Elimine la premi�re face de l'ensemble des faces d'un noeud
  public void eliminePremiereFace ( Vector ensembleFace ) {
    ensembleFace.remove( ensembleFace.firstElement() );
  }

  // Calcul les g�n�rateurs d'un noeud
  public Vector modificationGenerateurs ( Intent faceCourante, Vector ensembleGenerateur, Vector resultatBloqueueurMinimaux, Vector resultatBloqueur ) {
		
     // Parcours de l'ensemble des g�n�rateurs
      Iterator it = ensembleGenerateur.iterator();
      while ( it.hasNext() ) {
        Intent generateurCourant = (Intent)it.next();
		
        // Intersection entre la face courante et le g�n�rateur courant
        Intent intersection = this.intersectionGenerateurFaceVide( generateurCourant, faceCourante );
        if ( intersection.size() == 0 ) {
          
          Vector nouvelEnsembleGenerateur = this.parcoursItemsFace ( faceCourante, generateurCourant );
          this.ajouteGenerateurs( resultatBloqueur , nouvelEnsembleGenerateur );


        } else {
          resultatBloqueueurMinimaux.add( generateurCourant );
        }
      }
      if ( resultatBloqueur.size() == 0 ) {
        return resultatBloqueueurMinimaux;
      } else {
        if ( resultatBloqueueurMinimaux.size() == 0  ) {
          return resultatBloqueur;
        } else {
          Vector resultat = new Vector();
          this.estDejaGenerateur( resultatBloqueur, resultat, resultatBloqueueurMinimaux );
          resultatBloqueur.removeAll( resultat );
          this.ajouteGenerateurs( resultatBloqueueurMinimaux , resultatBloqueur );
          return  resultatBloqueueurMinimaux;
        }
      }
  }

  // Effectue l'union du g�n�rateur courant avec chacun des attributs du g�n�rateur courant
   public Vector parcoursItemsFace ( Intent faceCourante, Intent generateurCourant ) {
    // Parcours de l'ensemble des faces
    Vector resultat = new Vector();
    for (FormalAttribute itemFace : faceCourante) {
      Intent itemsetFace = new SetIntent();
      itemsetFace.add( itemFace );
      Intent bloqueur = this.calculNouveauGenerateur( generateurCourant, itemsetFace );
      // Ajout du nouveau g�n�rateur (union du g�n�rateur courant avec la face courante)
      resultat.add( bloqueur );
    }
    return resultat;
  }

  // Calcul des g�n�rateurs pour l'ensemble des noeuds
  public List calculGenerateursNoeud( Node<Concept> genConceptNode ) {
    if ( genConceptNode.getContent().getIntent().size()!=0 ) {
   
    Vector ensembleFaces = this.calculFace( genConceptNode );
    if ( ensembleFaces.size()!= 0 ) {

      // S�lection de la premi�re face et initialisation de l'ensemble des g�n�rateurs
      Intent premiereFace = this.retournePremierFace( ensembleFaces );
      Vector ensembleGenerateur = this.retourneItemItemset( premiereFace );

      // Elimination de la premi�re face
      this.eliminePremiereFace( ensembleFaces );
      Vector temporaire = new Vector();
      
      if ( ensembleFaces.size()!= 0 ) {
        Iterator it = ensembleFaces.iterator();
        while ( it.hasNext() ) {

          Intent faceCourante = (Intent)it.next();
          
          // Calcul de l'ensemble des g�n�rateurs du noeud courant
          Vector bloqueursMinimaux = new Vector();
          Vector bloqueurs = new Vector();
          Vector res = this.modificationGenerateurs( faceCourante, ensembleGenerateur, bloqueursMinimaux , bloqueurs );
          ensembleGenerateur = res;
          genConceptNode.getContent().setGenerator( ensembleGenerateur );
        }
      } else {
        genConceptNode.getContent().setGenerator( ensembleGenerateur );
      }
    } else {
      // Les g�n�rateurs du noeud courant correspondent a l'ensemble des items de l'intent du noeud courant
       genConceptNode.getContent().setGenerator( this.retourneItemItemset( genConceptNode.getContent().getIntent() ));
    }
    }
    return genConceptNode.getContent().getGenerator();
  }


  // Calcul des g�n�rateurs pour l'ensemble des noeuds
  public void calculGenerateurs() {

	int nbMaxNode=instanceTreillis.size();
	int numNodeCurrent=0;


    // Parcours de l'ensemble des ferm�s
    Iterator it = this.instanceTreillis.iterator();
    List resultat = new Vector();
    int i = 0;
    while ( it.hasNext() ) {

      // S�lection du noeud courant
      ConceptNode noeudCourant = (ConceptNode)it.next();
      
      // Calcul de son ensemble de g�n�rateurs
      boolean nb = false;
      resultat = this.calculGenerateursNoeud( noeudCourant );
      // Incr�mentation du nombre de g�n�rateurs
      this.nombreGenerateurs = this.nombreGenerateurs + resultat.size();

	  numNodeCurrent++;
	  sendJobPercentage((numNodeCurrent*100)/nbMaxNode);

    }
  }
  

   public void estDejaGenerateur( Vector ensembleGenerateurs, Vector resultat, Vector generateurs ) {
    Iterator it1 = ensembleGenerateurs.iterator();
    while (  it1.hasNext() ) {
      Intent generateurCourant = (Intent)it1.next();
      Iterator it2 = generateurs.iterator();
      boolean reponse = false;
      while ( ( it2.hasNext() )&& ( reponse == false ) ) {

         Intent generateur = (Intent)it2.next();
         if ( generateurCourant.containsAll( generateur ) ) {
          resultat.add( generateurCourant );
          reponse = true;
         }
      }
    }
  }
  
  public void ajouteGenerateurs( Vector vector1, Vector Vector2 ) {
    Iterator it1 = Vector2 .iterator();
    while (  it1.hasNext() ) {
      Intent courant = (Intent)it1.next();
      vector1.add( courant );
    }
  }
	/* (non-Javadoc)
	 * @see lattice.util.tooltask.JobObservable#getDescription()
	 */
	public String getDescription() {
		return "Jen for generator computation";
	}

	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		calculGenerateurs();
		if(jobObserv!=null) jobObserv.jobEnd(true);
	}

}

