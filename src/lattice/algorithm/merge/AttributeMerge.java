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

package lattice.algorithm.merge;

/**
 * <p>
 * Titre : Fusion de 2 treillis par les attributs
 * </p>
 * <p>
 * Description : PetkoInc (plate forme)
 * </p>
 * <p>
 * Copyright : Copyright (c) 2003
 * </p>
 * <p>
 * Société : UQAM - UdM
 * </p>
 * 
 * @author Céline FRAMBOURG
 * @version 2.0
 */

import java.util.Iterator;
import java.util.Vector;
import java.util.Hashtable;
import javax.swing.JFrame;
import javax.swing.JOptionPane;

import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.SetIntent;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.CompleteConceptLatticeImp;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;

public class AttributeMerge {

    // Partitionne du vecteur rentré en paramètre en deux sous-vecteurs
    private static int partitionDecroissant(Vector vecteur, int inf, int sup) {
        // Pivot correspond a la taille de l'itemset d'un noeud du vecteur non
        // trié
        ConceptNode noeudPivot = (ConceptNode) vecteur
                .elementAt((inf + sup) / 2);
        int taillePivot = noeudPivot.getContent().getIntent().size();

        int i = inf - 1;
        int j = sup + 1;
        ConceptNode temp = null;

        // Tant que les index ne se croisent pas
        while (i < j) {

            // Conserver les noeuds ayant une taille d'itemset inférieure ou
            // égale a la taille pivot
            do {
                i++;
            } while (((ConceptNode) vecteur.elementAt(i)).getContent()
                    .getIntent().size() > taillePivot);

            // Conserver les noeuds ayant une taille d'itemset supérieure ou
            // égale a la taille pivot
            do {
                j--;
            } while (((ConceptNode) vecteur.elementAt(j)).getContent()
                    .getIntent().size() < taillePivot);

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
    private static void quicksortDecroissant(Vector vecteur, int inf, int sup) {
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
    private static int partitionCroissant(Vector vecteur, int inf, int sup) {
        // Pivot correspond a la taille de l'itemset d'un noeud du vecteur non
        // trié
        ConceptNode noeudPivot = (ConceptNode) vecteur
                .elementAt((inf + sup) / 2);
        int taillePivot = noeudPivot.getContent().getIntent().size();

        int i = inf - 1;
        int j = sup + 1;
        ConceptNode temp = null;

        // Tant que les index ne se croisent pas
        while (i < j) {

            // Conserver les noeuds ayant une taille d'itemset inférieure ou
            // égale a la taille pivot
            do {
                i++;
            } while (((ConceptNode) vecteur.elementAt(i)).getContent()
                    .getIntent().size() < taillePivot);

            // Conserver les noeuds ayant une taille d'itemset supérieure ou
            // égale a la taille pivot
            do {
                j--;
            } while (((ConceptNode) vecteur.elementAt(j)).getContent()
                    .getIntent().size() > taillePivot);

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
    private static void quicksortCroissant(Vector vecteur, int inf, int sup) {

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

    private static Vector lowerCovers(ConceptNode n1, ConceptNode n2) {
        Vector res = new Vector();
        Iterator it = n1.getChildren().iterator();
        while (it.hasNext()) {
            ConceptNode[] couple = new ConceptNode[2];
            couple[0] = (ConceptNode) it.next();
            couple[1] = n2;
            res.add(couple);
        }
        it = n2.getChildren().iterator();
        while (it.hasNext()) {
            ConceptNode[] couple = new ConceptNode[2];
            couple[0] = n1;
            couple[1] = (ConceptNode) it.next();
            res.add(couple);
        }
        return res;
    }

    private static Vector maxClosed(ConceptNode first, Vector candidate) {
        Vector maxClo = new Vector();
        Intent firstIntent = first.getContent().getIntent();
        Intent face = (Intent) (firstIntent.clone());
        int size = candidate.size();
        for (int i = 0; i < size; i++) {
            ConceptNode nodCBar = (ConceptNode) candidate.get(i);
            Intent intCBar = nodCBar.getContent().getIntent();
            if ((firstIntent.toString()).equals((face
                    .intentIntersection(intCBar)).toString())) {
                maxClo.add((ConceptNode) (candidate.get(i)));
                face = face.intentUnion(intCBar);
            }
        }
        return maxClo;
    }

    private static Vector psi(ConceptNode n1, ConceptNode n2,
                              ConceptNode[][] psis, Vector v,
                              Hashtable indPsi1, Hashtable indPsi2) {
        Vector res = new Vector();
        int i = 1;
        Iterator it = v.iterator();
        while (it.hasNext()) {
            ConceptNode[] couple = (ConceptNode[]) it.next();
            Extent extent = couple[0].getContent().getExtent()
                    .extentIntersection(couple[1].getContent().getExtent());
            Intent intent = new SetIntent();
            ConceptNode n = null;
            Iterator itS = couple[0].getChildren().iterator();
            while (itS.hasNext()) {
                ConceptNode sC = (ConceptNode) itS.next();
                if ((psis[((Integer) indPsi1.get(sC)).intValue()][((Integer) indPsi2
                        .get(couple[1])).intValue()]).getContent().getExtent()
                        .size() == extent.size())
                    n = psis[((Integer) indPsi1.get(sC)).intValue()][((Integer) indPsi2
                            .get(couple[1])).intValue()];
            }
            if (n == null) {
                itS = couple[1].getChildren().iterator();
                while (itS.hasNext()) {
                    ConceptNode sC = (ConceptNode) itS.next();
                    if ((psis[((Integer) indPsi1.get(couple[0])).intValue()][((Integer) indPsi2
                            .get(sC)).intValue()]).getContent().getExtent()
                            .size() == extent.size())
                        n = psis[((Integer) indPsi1.get(couple[0])).intValue()][((Integer) indPsi2
                                .get(sC)).intValue()];
                }
            }
            if (n == null) {
                if ((psis[((Integer) indPsi1.get(couple[0])).intValue()][((Integer) indPsi2
                        .get(couple[1])).intValue()]) != null)
                    n = psis[((Integer) indPsi1.get(couple[0])).intValue()][((Integer) indPsi2
                            .get(couple[1])).intValue()];
                else {
                    intent = couple[0].getContent().getIntent()
                            .intentUnion(couple[1].getContent().getIntent());
                    n = new ConceptNodeImp(new ConceptImp(extent, intent));
                }
            }
            psis[((Integer) indPsi1.get(couple[0])).intValue()][((Integer) indPsi2
                    .get(couple[1])).intValue()] = n;
            if (!(res.contains(n)))
                res.add(n);
        }
        return res;
    }

    private static ConceptNode findPsi(Extent extent, Vector candidates) {
        int a = extent.size();
        Iterator it = candidates.iterator();
        while (it.hasNext()) {
            ConceptNode n = (ConceptNode) it.next();
            if (n.getContent().getExtent().size() == a)
                return n;
        }
        return null;
    }

    private static ConceptNode find(ConceptNode n, CompleteConceptLattice l) {
        Iterator it = ((Vector) l.getIntentLevelIndex()
                .get(n.getContent().getIntent().size())).iterator();
        while (it.hasNext()) {
            ConceptNode nC = (ConceptNode) it.next();
            if (nC.equals(n))
                return nC;
        }
        return null;
    }

    public static MatrixBinaryRelationBuilder createBR(MatrixBinaryRelationBuilder br1, MatrixBinaryRelationBuilder br2) {
        MatrixBinaryRelationBuilder br = new MatrixBinaryRelationBuilder(
                                               br1.getObjectsNumber(),
                                               br1.getAttributesNumber()
                                                       + br2
                                                               .getAttributesNumber());
        br.setName("contexte du treillis résultant de la fusion");
        for (int i = 0; i < br.getObjectsNumber(); i++) {
            try {
                br.replaceObject(i, (FormalObject) br1.getObjects().get(i));
            } catch (BadInputDataException ex) {
            }
        }
        int k = 0;
        for (int i = 0; i < br1.getAttributesNumber(); i++) {
            try {
                br.replaceAttribute(i, (FormalAttribute) br1.getAttributes()
                        .get(k));
            } catch (BadInputDataException ex) {
            }
            k++;
        }
        k = 0;
        for (int i = br1.getAttributesNumber(); i < br1.getAttributesNumber()
                                                    + br2.getAttributesNumber(); i++) {
            try {
                br.replaceAttribute(i, (FormalAttribute) br2.getAttributes()
                        .get(k));

            } catch (BadInputDataException ex) {
            }
            k++;
        }
        k = 0;
        for (int i = 0; i < br1.getAttributesNumber(); i++) {
            for (int j = 0; j < br.getObjectsNumber(); j++) {
                try {
                    br.setRelation((FormalObject) br.getObjects().get(j),
                                   (FormalAttribute) br.getAttributes().get(i),
                                   br1.getRelation(k, i));
                } catch (BadInputDataException ex) {
                }
            }
            k++;
        }
        k = 0;
        for (int i = br1.getAttributesNumber(); i < br1.getAttributesNumber()
                                                    + br2.getAttributesNumber(); i++) {
            for (int j = 0; j < br.getObjectsNumber(); j++) {
                try {
                    br.setRelation((FormalObject) br.getObjects().get(j),
                                   (FormalAttribute) br.getAttributes().get(i),
                                   br2.getRelation(j, k));
                } catch (BadInputDataException ex) {
                }
            }
            k++;
        }
        return br;
    }

    public static CompleteConceptLattice fusionne(CompleteConceptLattice l1,
                                                  CompleteConceptLattice l2,
                                                  MatrixBinaryRelationBuilder br1,
                                                  MatrixBinaryRelationBuilder br2) {
        if (!(l1.getTop().getContent().getExtent().equals(l2.getTop()
                .getContent().getExtent()))) {
            JFrame frame = new JFrame();
            JOptionPane
                    .showMessageDialog(frame,
                                       "The two lattices don't have the same objects");
            return null;
        } else {
            Intent intersection = l1
                    .getBottom()
                    .getContent()
                    .getIntent()
                    .intentIntersection(l2.getBottom().getContent().getIntent());
            if (intersection.size() != 0) {
                Iterator it = intersection.iterator();
                while (it.hasNext()) {
                    FormalAttribute fa = (FormalAttribute) it.next();
                    if (br1.getExtent(fa).extentIntersection(br2.getExtent(fa)).size() != br1
                            .getExtent(fa).size()) {
                        JFrame frame = new JFrame();
                        JOptionPane
                                .showMessageDialog(frame,
                                                   "You have two common attributes with different tidset");

                        return null;
                    }
                }
            }
            Hashtable indPsi1 = new Hashtable();
            Hashtable indPsi2 = new Hashtable();
            int j = 0;
            int k = 0;
            ConceptNode[][] psis = new ConceptNode[l1.size()][l2.size()];
            Extent bottomExtent = l1
                    .getBottom()
                    .getContent()
                    .getExtent()
                    .extentIntersection(l2.getBottom().getContent().getExtent());
            Intent topIntent = l1.getTop().getContent().getIntent()
                    .intentUnion(l2.getTop().getContent().getIntent());
            CompleteConceptLattice l3 = new CompleteConceptLatticeImp();
            l3.initialiseIntentLevelIndex(l1.getBottom().getContent()
                    .getIntent().intentUnion(
                                             l2.getBottom().getContent()
                                                     .getIntent()).size() + 1);
            // Parcours du premier treillis
            for (int i = l1.getBottom().getContent().getIntent().size() + 1; i != 0; i--) {
                Iterator it1 = l1.getIntentLevelIndex().get(i - 1).iterator();
                while (it1.hasNext()) {
                    ConceptNode n1 = (ConceptNode) it1.next();
                    indPsi1.put(n1, new Integer(j++));
                    for (int m = l2.getBottom().getContent().getIntent().size() + 1; m != 0; m--) {
                        Iterator it2 = l2.getIntentLevelIndex().get(m - 1)
                                .iterator();
                        // Parcours du deuxième treillis
                        while (it2.hasNext()) {
                            ConceptNode n2 = (ConceptNode) it2.next();
                            if (indPsi2.get(n2) == null) {
                                indPsi2.put(n2, new Integer(k++));
                            }
                            Extent extent = n1.getContent().getExtent()
                                    .extentIntersection(
                                                        n2.getContent()
                                                                .getExtent());
                            Vector psiImages = psi(n1, n2, psis,
                                                   lowerCovers(n1, n2),
                                                   indPsi1, indPsi2);
                            // Tri des concepts de psiImages par taille d'intent
                            // croissante
                            quicksortCroissant(psiImages, 0,
                                               psiImages.size() - 1);
                            if (findPsi(extent, psiImages) == null) {
                                ConceptNode n = new ConceptNodeImp(
                                                                   new ConceptImp(
                                                                                  extent,
                                                                                  n1
                                                                                          .getContent()
                                                                                          .getIntent()
                                                                                          .intentUnion(
                                                                                                       n2
                                                                                                               .getContent()
                                                                                                               .getIntent())));
                                // Calcul des parents
                                Iterator it = maxClosed(n, psiImages)
                                        .iterator();
                                while (it.hasNext()) {
                                    ConceptNode nU = find((ConceptNode) it
                                            .next(), l3);
                                    l3.setUpperCover(n, nU);
                                }
                                // Insertion dans le treillis
                                l3.incNbOfNodes();
                                l3.add(n);
                                if (n.getContent().getExtent().size() == bottomExtent
                                        .size())
                                    l3.setBottom(n);
                                if (n.getContent().getIntent().size() == topIntent
                                        .size())
                                    l3.setTop(n);
                            }
                        }
                    }
                }
            }
            return l3;
        }
    }
}
