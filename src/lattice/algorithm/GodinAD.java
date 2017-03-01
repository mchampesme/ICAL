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

package lattice.algorithm;

import java.util.List;
import java.util.Vector;

import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.DefaultFormalObject;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.CompleteConceptLatticeImp;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
import lattice.util.structure.Node;

/**
 *
 * <p>Titre : Lattice</p>
 * <p>Description : Manipulation des treillis</p>
 * <p>Copyright : Copyright (c) 2003</p>
 * <p>Société : Université de Montréal</p>
 * @author Anna Tkachenko reviewed by Céline Frambourg
 * @version 1.0
 */
public class GodinAD
    extends LatticeAlgorithmInc {
  private MatrixBinaryRelationBuilder br;
  CompleteConceptLattice treillis;
  List<List<Node<Concept>>> li1; // structure auxiliaire pour réduire le nommbre d'appels de la
  // fonction treillis.get_intent_level_index() (:= C dans la reference)

  /**
   *
   *CONSTRUCTEUR
   */
  public GodinAD(MatrixBinaryRelationBuilder br) {
    super(br);
    this.br = br;
  }

  /**
   * Méthode héritée de la classe supérieure
   * Retourne la description de l'algo
   * @return description
   */
  public String getDescription() {
    return "Godin incremental lattice update";
  }

  /**
   * Méthode héritée de la classe supérieure
   * La fonction principale:
   *    extraire l'objet et son ensemble d'attributs
   *    de la relation binaire et appeler l'algorithme de Godin
   */
  public void doAlgorithm() {
	ConceptNodeImp.resetNodeId();
    long time = System.currentTimeMillis(); // TIMER

    int nbObjets = br.getObjectsNumber();
    treillis = getLattice();
    li1 = treillis.getIntentLevelIndex();

    for (int i = 0; i < nbObjets; i++) {
      FormalObject o = new DefaultFormalObject(null);
      o = br.getFormalObject(i);
      doGodin1(o, br.getIntent(o));
      sendJobPercentage(i * 100 / nbObjets); // gestion de la progression
    }
    System.out.println("FIN " + (System.currentTimeMillis() - time) + " mSec."); // fin TIMER
    System.out.println("Nombres de concepts : " + getLattice().size());
    /*
      // Juste pour tester
      for(int i = 0; i < li1.size(); i++)
      for(int k = 0; k < ((Vector)li1.elementAt(i)).size(); k++) {
      Node n = ((Node)((Vector)li1.elementAt(i)).elementAt(k));
      System.out.println("ID = " + n.getId() + " " + n.getConcept()
      + "  Parents: " + n.getParents()
      + "  Enfants: " + n.getChildren());
      } // fin test
     */
  }

  /**
   * Implémentation de l'algorithme de Godin
   * Arguments: un objet avec l'ensemble de ses attributs
   * @param objet
   * @param intent
   */
  public void doGodin1(FormalObject objet, Intent intent) {
    Extent extent = new SetExtent();
    extent.add(objet); // transformer l'objet en entension
    ConceptImp concept = new ConceptImp(extent, intent); // former un concept

    if (treillis.getBottom() == null) {
      // Initialiser un nouveau treillis avec le premier concept formé
      treillis.setBottom(new ConceptNodeImp(concept)); // remplacer le supremum null par le premier noeud
      treillis.setTop(treillis.getBottom());
      treillis.initialiseIntentLevelIndex(intent.size() + 1); // initialser li1
      treillis.set_max_transaction_size(intent.size());
      treillis.add(treillis.getBottom()); // inserer le supremum dans li1
      treillis.incNbOfNodes();
    }
    else {
      // mise a jour du sup(G) du treillis, du li1 et des liens...
      //treillis.adjustBottom(concept);

      ConceptNodeImp bottom = (ConceptNodeImp) treillis.getBottom();
      int intBottomSize = bottom.getContent().getIntent().size();
      if (!bottom.getContent().getIntent().containsAll(concept.getIntent())) {
        if (bottom.getContent().getExtent().isEmpty()) {
          bottom.getContent().getIntent().addAll(concept.getIntent());
          //( (CompleteConceptLatticeImp) treillis).adjustMaxIntentLevelIndex(concept);
          getLattice().remove(bottom);
          adjustMaxIntentLevelIndex(( (CompleteConceptLatticeImp) treillis),(ConceptImp) bottom.getContent());
          getLattice().add(bottom);
        }

        else {
          ConceptNodeImp node = new ConceptNodeImp(new ConceptImp(new SetExtent(),
              bottom.getContent().getIntent().intentUnion(concept.getIntent())));
          node.parents.add(bottom);
          bottom.getChildren().add(node);
          treillis.setBottom(node);
          treillis.getBottom().setVisited(true);
          for (int i=intBottomSize; i < treillis.getBottom().getContent().getIntent().size();i++ )
            li1.add(new Vector<Node<Concept>>());
          li1.get(li1.size() - 1).add(treillis.getBottom());
         adjustMaxIntentLevelIndex(treillis , treillis.getBottom().getContent());
          getLattice().add(treillis.getBottom());
          treillis.incNbOfNodes();
        }
      }

      Vector[] li2 = new Vector[intent.size() + 1]; // := C' dans la reference
      for (int i = 0; i < li2.length; i++)
        li2[i] = new Vector();

        // Traiter chaque bloc de noeuds en ordre
        // croissant de leur cardinalite
      for (int i = 0; i < li1.size(); i++) {

        for (int m = 0; m < li1.get(i).size(); m++) {

          Node<Concept> nd = li1.get(i).get(m);
          if (intent.containsAll(nd.getContent().getIntent())) { // modifié
            nd.getContent().getExtent().add(objet);
            li2[i].add(nd);
            if (nd.getContent().getIntent().equals(intent)) {
              treillis.setTop(treillis.findTop());
              return;
            }
          }

          else { // ancienne paire
            Intent itn = (nd.getContent().getIntent()).intentIntersection(intent);

            if (isAGenerator(itn, li2)) { // si nd est un generateur
                Node<Concept> newNoeud = new ConceptNodeImp(new ConceptImp(nd.getContent().
                  getExtent().extentUnion(extent), itn));
              newNoeud.getContent().getExtent().add(objet);
              treillis.add(newNoeud);
              li2[itn.size()].add(newNoeud);
            modifyEdges(nd, newNoeud, li2); // modifier les arcs
              treillis.incNbOfNodes();

              if (itn.equals(intent)) {
                treillis.setTop(treillis.findTop());
                return;
              }
            }
          }
        }
      } // fin for
      treillis.setTop(treillis.findTop());
    } // fin else
  } // fin doGodin

/* (non-Javadoc)
 * @see lattice.algorithm.LatticeAlgorithmInc#addConcept(lattice.util.ConceptImp)
 */
public void addConcept(Concept c) {
	// TODO Auto-generated method stub
	
}
}
