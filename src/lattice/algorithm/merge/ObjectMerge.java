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

package lattice.algorithm.merge;

/**
 * <p>Titre : Fusion de 2 treillis</p>
 * <p>Description : PetkoInc (plate forme)</p>
 * <p>Copyright : Copyright (c) 2003</p>
 * <p>Société : UQAM - UdM</p>
 * @author Céline FRAMBOURG
 * @version 2.0
 */

import java.util.Iterator;
import java.util.Vector;
import java.util.Hashtable;
import javax.swing.JFrame;
import javax.swing.JOptionPane;

import rule.generator.ValtchevAlOnlineGeneratorUpdate;
import rule.generator.Jen;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.CompleteConceptLatticeImp;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;

public class ObjectMerge {

  // Partitionne du vecteur rentré en paramètre en deux sous-vecteurs
  private static int partitionDecroissant(Vector vecteur, int inf,
                                          int sup) {
    // Pivot correspond a la taille de l'itemset d'un noeud du vecteur non trié
    ConceptNode noeudPivot = (ConceptNode) vecteur.elementAt( (inf + sup) /
                                               2);
    int taillePivot = noeudPivot.getContent().getIntent().size();

    int i = inf - 1;
    int j = sup + 1;
    ConceptNode temp = null;

    // Tant que les index ne se croisent pas
    while (i < j) {

      // Conserver les noeuds ayant une taille d'itemset inférieure ou égale a la taille pivot
      do {
        i++;
      }
      while ( ( (ConceptNode) vecteur.elementAt(i)).getContent().getIntent().size() >
             taillePivot);

      // Conserver les noeuds ayant une taille d'itemset supérieure ou égale a la taille pivot
      do {
        j--;
      }
      while ( ( (ConceptNode) vecteur.elementAt(j)).getContent().getIntent().size() <
             taillePivot);

      // Permuter les noeuds qui ne sont pas a leur place
      if (i < j) {
        temp = (ConceptNode) vecteur.elementAt(i);
        vecteur.set(i, (ConceptNode) vecteur.elementAt(j));
        vecteur.set(j, temp);
      }
    }
    // Indice correspondant a la subdivision dans le vecteur
    return j;
  }

// Trie suivant les itemsets croissants a partir du partitionnement
  private static void quicksortDecroissant(Vector vecteur, int inf,
                                           int sup) {
    // Itemset délimitant les deux parties du vecteur
    int milieu = 0;

    // S'il y a au moins deux noeuds
    if (sup > inf) {
      milieu = partitionDecroissant(vecteur, inf, sup);

      // Tri de la partie gauche du vecteur
      quicksortDecroissant(vecteur, inf, milieu);

      // Tri de la partie droite du vecteur
      quicksortDecroissant(vecteur, milieu + 1, sup);
    }
  }

  // Partitionne du vecteur rentré en paramètre en deux sous-vecteurs
  private static int partitionCroissant(Vector vecteur, int inf,
                                        int sup) {
    // Pivot correspond a la taille de l'itemset d'un noeud du vecteur non trié
    ConceptNode noeudPivot = (ConceptNode) vecteur.elementAt( (inf + sup) /
                                               2);
    int taillePivot = noeudPivot.getContent().getIntent().size();

    int i = inf - 1;
    int j = sup + 1;
    ConceptNode temp = null;

    // Tant que les index ne se croisent pas
    while (i < j) {

      // Conserver les noeuds ayant une taille d'itemset inférieure ou égale a la taille pivot
      do {
        i++;
      }
      while ( ( (ConceptNode) vecteur.elementAt(i)).getContent().getIntent().size() <
             taillePivot);

      // Conserver les noeuds ayant une taille d'itemset supérieure ou égale a la taille pivot
      do {
        j--;
      }
      while ( ( (ConceptNode) vecteur.elementAt(j)).getContent().getIntent().size() >
             taillePivot);

      // Permuter les noeuds qui ne sont pas a leur place
      if (i < j) {
        temp = (ConceptNode) vecteur.elementAt(i);
        vecteur.set(i, (ConceptNode) vecteur.elementAt(j));
        vecteur.set(j, temp);
      }
    }
    // Indice correspondant a la subdivision dans le vecteur
    return j;
  }

// Trie suivant les itemsets croissants a partir du partitionnement
  private static void quicksortCroissant(Vector vecteur, int inf,
                                         int sup) {

    // Itemset délimitant les deux parties du vecteur
    int milieu = 0;

    // S'il y a au moins deux noeuds
    if (sup > inf) {
      milieu = partitionCroissant(vecteur, inf, sup);

      // Tri de la partie gauche du vecteur
      quicksortCroissant(vecteur, inf, milieu);

      // Tri de la partie droite du vecteur
      quicksortCroissant(vecteur, milieu + 1, sup);
    }
  }

  private static Vector upperCovers(ConceptNode n1, ConceptNode n2) {
    Vector res = new Vector();
    Iterator it = n1.getParents().iterator();
    while (it.hasNext()) {
      ConceptNode[] couple = new ConceptNode[2];
      couple[0] = (ConceptNode) it.next();
      couple[1] = n2;
      res.add(couple);
    }
    it = n2.getParents().iterator();
    while (it.hasNext()) {
      ConceptNode[] couple = new ConceptNode[2];
      couple[0] = n1;
      couple[1] = (ConceptNode) it.next();
      res.add(couple);
    }
    return res;
  }

  private static Vector minClosed(ConceptNode first, Vector candidate) {
    Vector minClo = new Vector();
    Extent firstExtent = first.getContent().getExtent();
    Extent face = (Extent) (firstExtent.clone());
    int size = candidate.size();
    for (int i = 0; i < size; i++) {
      ConceptNode nodCBar = (ConceptNode) candidate.get(i);
      Extent extCBar = nodCBar.getContent().getExtent();
      if ( (firstExtent.toString()).equals( (face.extentIntersection(extCBar)).
                                           toString())) {
        minClo.add( (ConceptNode) (candidate.get(i)));
        face = face.extentUnion(extCBar);
      }
    }
    return minClo;
  }

  private static Vector psi(ConceptNode n1, ConceptNode n2, ConceptNode[][] psis, Vector v,
                            Hashtable indPsi1, Hashtable indPsi2) {
    Vector res = new Vector();
    int i = 1;
    Iterator it = v.iterator();
    while (it.hasNext()) {
      ConceptNode[] couple = (ConceptNode[]) it.next();
      Intent intent = couple[0].getContent().getIntent().intentIntersection(couple[1].
          getContent().getIntent());
      Extent extent = new SetExtent();
      ConceptNode n = null;
      Iterator itS = couple[0].getParents().iterator();
      while (itS.hasNext()) {
        ConceptNode sC = (ConceptNode) itS.next();
        if ( (psis[ ( (Integer) indPsi1.get(sC)).intValue()][ ( (Integer) indPsi2.get(
            couple[1])).intValue()]).getContent().getIntent().size() ==
            intent.size())
          n = psis[ ( (Integer) indPsi1.get(sC)).intValue()][ ( (Integer) indPsi2.get(
              couple[1])).intValue()];
      }
      if (n == null) {
        itS = couple[1].getParents().iterator();
        while (itS.hasNext()) {
          ConceptNode sC = (ConceptNode) itS.next();
          if ( (psis[ ( (Integer) indPsi1.get(couple[0])).intValue()][ ( (Integer)
              indPsi2.get(sC)).intValue()]).getContent().getIntent().size() ==
              intent.size())
            n = psis[ ( (Integer) indPsi1.get(couple[0])).intValue()][ ( (Integer)
                indPsi2.get(sC)).intValue()];
        }
      }
      if (n == null) {
        if ( (psis[ ( (Integer) indPsi1.get(couple[0])).intValue()][ ( (Integer) indPsi2.
            get(couple[1])).intValue()]) != null)
          n = psis[ ( (Integer) indPsi1.get(couple[0])).intValue()][ ( (Integer) indPsi2.
              get(couple[1])).intValue()];
        else {
          extent = couple[0].getContent().getExtent().extentUnion(
              couple[1].getContent().getExtent());
          n = new ConceptNodeImp(new ConceptImp(extent, intent));
        }
      }
      psis[ ( (Integer) indPsi1.get(couple[0])).intValue()][ ( (Integer) indPsi2.get(
          couple[1])).intValue()] = n;
      if (! (res.contains(n)))
        res.add(n);
    }
    return res;
  }

  private static ConceptNode findPsi(Intent intent, Vector candidates) {
    int a = intent.size();
    Iterator it = candidates.iterator();
    while (it.hasNext()) {
      ConceptNode n = (ConceptNode) it.next();
      if (n.getContent().getIntent().size() == a)
        return n;
    }
    return null;
  }

    private static ConceptNode find(ConceptNode n, CompleteConceptLattice l) {
      Iterator it = ( (Vector) l.getIntentLevelIndex().get(n.getContent().
          getIntent().size())).iterator();
      while (it.hasNext()) {
        ConceptNode nC = (ConceptNode) it.next();
        if (nC.equals(n))
          return nC;
      }
      return null;
    }

    public static MatrixBinaryRelationBuilder createBR(MatrixBinaryRelationBuilder br1, MatrixBinaryRelationBuilder br2) {
      MatrixBinaryRelationBuilder br = new MatrixBinaryRelationBuilder(br1.getObjectsNumber() +
                                             br2.getObjectsNumber(),
                                           br1.getAttributesNumber());
      br.setName("contexte du treillis résultant de la fusion");
      for (int i = 0; i < br.getAttributesNumber(); i++) {
        try {
          br.replaceAttribute(i,
                              (FormalAttribute) br1.getAttributes().
                              get(i));
        }
        catch (BadInputDataException ex) {
        }
      }
      int k = 0;
      for (int i = 0; i < br1.getObjectsNumber(); i++) {
        try {
          br.replaceObject(i,
                           (FormalObject) br1.getObjects().
                           get(k));
        }
        catch (BadInputDataException ex) {
        }
        k++;
      }
      k = 0;
      for (int i = br1.getObjectsNumber(); i < br1.getObjectsNumber() + br2.getObjectsNumber(); i++) {
        try {
          br.replaceObject(i,
                           (FormalObject) br2.getObjects().
                           get(k));
        }
        catch (BadInputDataException ex) {
        }
        k++;
      }
      k = 0;
      for (int i = 0; i < br1.getObjectsNumber(); i++) {
        for (int j = 0; j < br.getAttributesNumber(); j++) {
          try {
            br.setRelation( (FormalObject) br.getObjects().
                           get(i), (FormalAttribute) br.getAttributes().
                           get(j), br1.getRelation(k, j));
          }
          catch (BadInputDataException ex) {
          }
        }
        k++;
      }
      k = 0;
      for (int i = br1.getObjectsNumber(); i < br1.getObjectsNumber() + br2.getObjectsNumber(); i++) {
        for (int j = 0; j < br.getAttributesNumber(); j++) {
          try {
            br.setRelation( (FormalObject) br.getObjects().
                            get(i), (FormalAttribute) br.getAttributes().
                            get(j), br2.getRelation(k, j));
          }
          catch (BadInputDataException ex) {
          }
        }
        k++;
      }

      return br;
    }


  public static CompleteConceptLattice fusionne(CompleteConceptLattice l1, CompleteConceptLattice l2, MatrixBinaryRelationBuilder br1, MatrixBinaryRelationBuilder br2,  boolean gens) {
    if (! (l1.getBottom().getContent().getIntent().equals(l2.getBottom().
        getContent().getIntent()))) {
      JFrame frame = new JFrame();
      JOptionPane.showMessageDialog(frame,
                                    "The two lattices don't have the same attributes");
      return null;
    }
    else {
      Extent intersection = l1.getTop().getContent().getExtent().extentIntersection(
          l2.getTop().getContent().getExtent());
      if (intersection.size() != 0) {
        Iterator it = intersection.iterator();
        while (it.hasNext()) {
          FormalObject fo = (FormalObject) it.next();
          if (br1.getIntent(fo).intentIntersection(br2.getIntent(fo)).size() != br1.getIntent(fo).size()) {
            JFrame frame = new JFrame();
            JOptionPane.showMessageDialog(frame,
                                          "You have two common objects with differents itemsets");

            return null;
          }
        }
      }
      Hashtable indPsi1 = new Hashtable();
      Hashtable indPsi2 = new Hashtable();
      int j = 0;
      int k = 0;
      ConceptNode[][] psis = new ConceptNode[l1.size()][l2.size()];
      Intent bottomIntent = l1.getBottom().getContent().getIntent().
          intentIntersection(l2.getBottom().getContent().getIntent());
      Extent topExtent = l1.getTop().getContent().getExtent().extentUnion(l2.
          getTop().
          getContent().getExtent());
      CompleteConceptLattice l3 = new CompleteConceptLatticeImp();
      l3.initialiseIntentLevelIndex(l1.getBottom().getContent().getIntent().
                                    size() + 1);
      // Parcours du premier treillis
      Iterator it1 = l1.iterator();
      while (it1.hasNext()) {
        ConceptNode n1 = (ConceptNode) it1.next();
        indPsi1.put(n1, new Integer(j++));
        Iterator it2 = l2.iterator();
        // Parcours du deuxième treillis
        while (it2.hasNext()) {
          ConceptNode n2 = (ConceptNode) it2.next();
          if (indPsi2.get(n2) == null) {
            indPsi2.put(n2, new Integer(k++));
          }
          Intent intent = n1.getContent().getIntent().intentIntersection(n2.
              getContent().getIntent());
          Vector psiImages = psi(n1, n2, psis, upperCovers(n1, n2), indPsi1,
                                 indPsi2);
          // Tri des concepts de psiImages par taille d'intent décroissante
          quicksortDecroissant(psiImages, 0, psiImages.size() - 1);
          if (findPsi(intent, psiImages) == null) {
            ConceptNode n = new ConceptNodeImp(new ConceptImp(n1.getContent().getExtent().
                                                 extentUnion(n2.getContent().
                                                       getExtent()), intent));
            // Calcul des parents
            Iterator it = minClosed(n, psiImages).iterator();
            while (it.hasNext()) {
              ConceptNode nU = find( (ConceptNode) it.next(), l3);
              l3.setUpperCover(nU, n);
            }
            // Calcul des générateurs
            if (gens) {
              if (! (n.getContent().getExtent().size() == 0)) {
                if (! (n1.equals(l1.getBottom())))
                	ValtchevAlOnlineGeneratorUpdate.computeGenerators((ConceptImp) n1.getContent(), (ConceptImp) n.getContent());
                else {
                  Jen jen = new Jen(l3);
                  jen.calculGenerateursNoeud(n);
                }
              }
            }
            // Insertion dans le treillis
            l3.incNbOfNodes();
            l3.add(n);
            if (n.getContent().getIntent().size() == bottomIntent.size())
              l3.setBottom(n);
            if (n.getContent().getExtent().size() == topExtent.size())
              l3.setTop(n);
          }
        }
      }
      return l3;
    }
  }

}
