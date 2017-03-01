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

package lattice.algorithm;

import java.util.List;
import java.util.Vector;

import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.CompleteConceptLatticeImp;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
import lattice.util.structure.LatticeNodeNR;
import lattice.util.structure.Node;

/**
 * <p>
 * Titre : Lattice
 * </p>
 * <p>
 * Description : Construction des treillis a l'aide de l'algorithme de Nourine &
 * Reynaud
 * </p>
 * <p>
 * Copyright : Copyright (c) 2003
 * </p>
 * <p>
 * Société : Université de Montréal
 * </p>
 * 
 * @author Dmitry Pestov
 * @version 1.0
 */
public class NouReynaud extends LatticeAlgorithmInc {
    private MatrixBinaryRelationBuilder br;

    private FormalObject[] objets;

    private FormalAttribute[] attributs;

    private CompleteConceptLattice treillis = getLattice();

    private List<List<Node<Concept>>> li1 = treillis.getIntentLevelIndex();

    private ExtentIndex extentIndex;

    // Tableau contenant les extensions des concepts attributs
    private Extent[] concAttributs;

    // CONSTRUCTEUR
    public NouReynaud(MatrixBinaryRelationBuilder br) {
        super(br);
        this.br = br;
    }

    // deux prochaines methodes sont héritées
    // de la classe supérieure
    public String getDescription() {
        return "Nourine & Reynaud lattice update";
    }

    /**
     *
     */
    public void doAlgorithm() {
        ConceptNodeImp.resetNodeId();
        long time = System.currentTimeMillis(); // Debut TIMER

        extentIndex = new ExtentIndex();
        objets = br.getFormalObjects();

        for (int i = 0; i < objets.length; i++) {
            FormalObject o = objets[i];
            doGodin(o, br.getIntent(o));
            sendJobPercentage(i * 50 / objets.length); // gestion de la
                                                        // progression
        }

        System.out.println("FIN Nourrine&Reynaud  - "
                           + (System.currentTimeMillis() - time) + " mSec."); // Fin
                                                                                // TIMER

        /*
         * // TEST System.out.println("EXTENTINDEX"); for(int j = 0; j <
         * extentIndex.size(); j++) for(int i = 0; i <
         * extentIndex.getAt(j).size(); i++)
         * System.out.println(((LatticeNodeNR)(extentIndex.getAt(j).elementAt(i))).getConcept());
         * System.out.println("\nLI1"); int num = 1; for(int j = 0; j <
         * li1.size(); j++) for(int i = 0; i <
         * ((Vector)li1.elementAt(j)).size(); i++) { System.out.println(num + " " +
         * ((LatticeNodeNR)((Vector)li1.elementAt(j)).elementAt(i)).toString() + " " +
         * ((LatticeNodeNR)((Vector)li1.elementAt(j)).elementAt(i)).getConcept());
         * num++; } // fin TEST
         */

        doNRalgo();

        System.out.println("FIN " + (System.currentTimeMillis() - time)
                           + " mSec."); // Fin TIMER
    }

    public void doNRalgo() {
        attributs = br.getFormalAttributes();

        // Construire le vecteur logeant les extensions des concepts attributs
        concAttributs = new Extent[attributs.length];

        for (int i = 0; i < attributs.length; i++)
            concAttributs[i] = br.getExtent(attributs[i]);

        // Mettre a 0 les compteurs associés aux noeuds (est-il vraiment
        // necessaire ?)
        // for(int i = 0; i < noeuds.size(); i++)
        // for(int k = 0; k < ((Vector)noeuds.elementAt(i)).size(); k++)
        // ((LatticeNodeNR)((Vector)noeuds.elementAt(i)).elementAt(k)).setCompteur(0);

        long total = 0;
        // Identifier la couverture des concepts
        for (int i = 0; i < extentIndex.size(); i++) {
            for (int j = 0; j < extentIndex.getAt(i).size(); j++) {
                ConceptNode noeud = (LatticeNodeNR) extentIndex.getAt(i)
                        .elementAt(j);

                Vector listNoeudsCandidats = new Vector();

                for (int k = 0; k < attributs.length; k++) {
                    if (!noeud.getContent().getIntent().contains(attributs[k])) {
                        Extent e = concAttributs[k].extentIntersection(noeud
                                .getContent().getExtent());

                        long tmp = System.currentTimeMillis();
                        LatticeNodeNR candidat = extentIndex
                                .trouverNoeudCandidat(e);
                        total = total + (System.currentTimeMillis() - tmp);

                        candidat.setCompteur(candidat.getCompteur() + 1);

                        if (candidat.getCompteur() == 1)
                            listNoeudsCandidats.add(candidat);

                        if (candidat.getCompteur()
                            + noeud.getContent().getIntent().size() == candidat
                                .getContent().getIntent().size())
                            treillis.setUpperCover(noeud, candidat);
                    }
                }

                for (int l = 0; l < listNoeudsCandidats.size(); l++)
                    ((LatticeNodeNR) listNoeudsCandidats.elementAt(l))
                            .setCompteur(0);
            }
            sendJobPercentage(50 + i * 50 / extentIndex.size()); // gestion
                                                                    // de la
                                                                    // progression
        }

        /*
         * // TEST for(int i = 0; i < treillis.get_intent_level_index().size();
         * i++) for(int j = 0; j <
         * ((Vector)treillis.get_intent_level_index().elementAt(i)).size(); j++)
         * System.out.println("NOEUD - " +
         * ((Node)(((Vector)treillis.get_intent_level_index().elementAt(i)).elementAt(j))).getConcept()); //
         * fin TEST
         */
        System.out.println("TOTAL CANDIDATS - " + total + " mSec.");
    } // fin doNRalgo

    private void doGodin(FormalObject objet, Intent intent) {
        Extent extent = new SetExtent();
        extent.add(objet); // transformer l'objet en extension
        ConceptImp concept = new ConceptImp(extent, intent);

        if (treillis.getBottom() == null) {
            LatticeNodeNR noeud = new LatticeNodeNR(concept);
            extentIndex.ajouterNoeud(noeud);

            // Initialiser un nouveau treillis avec le premier concept formé
            treillis.setBottom(noeud); // remplacer le supremum null par le
                                        // premier noeud
            treillis.setTop(noeud);
            treillis.initialiseIntentLevelIndex(intent.size() + 1); // initialser
                                                                    // li1
            treillis.set_max_transaction_size(intent.size());
            treillis.add(noeud); // inserer le supremum dans li1
            treillis.incNbOfNodes();
        }

        else {
            LatticeNodeNR bottom = (LatticeNodeNR) treillis.getBottom();

            if (!bottom.getContent().getIntent()
                    .containsAll(concept.getIntent())) {
                if (bottom.getContent().getExtent().isEmpty()) {
                    bottom.getContent().getIntent().addAll(concept.getIntent());
                    adjustMaxIntentLevelIndex(
                                              ((CompleteConceptLatticeImp) treillis),
                                              concept);
                }

                else {
                    bottom = new LatticeNodeNR(
                                               new ConceptImp(
                                                              new SetExtent(),
                                                              bottom
                                                                      .getContent()
                                                                      .getIntent()
                                                                      .intentUnion(
                                                                                   concept
                                                                                           .getIntent())));
                    treillis.setBottom(bottom);
                    treillis.getBottom().setVisited(true);
                    li1.add(new Vector<Node<Concept>>());
                    li1.get(li1.size() - 1).add(treillis.getBottom());
                    treillis.incNbOfNodes();

                    extentIndex.ajouterNoeud(bottom);
                }
            }

            Vector[] li2 = new Vector[intent.size() + 1]; // := C' dans la
                                                            // reference

            for (int i = 0; i < li2.length; i++)
                li2[i] = new Vector();

            for (int i = 0; i < li1.size(); i++)
                for (int m = 0; m < ((Vector) li1.get(i)).size(); m++) {
                    LatticeNodeNR nd = (LatticeNodeNR) li1.get(i).get(m);

                    if (intent.containsAll(nd.getContent().getIntent())) {
                        // Modifier la paire
                        extentIndex.effacerNoeud(nd);
                        nd.getContent().getExtent().add(objet);
                        li2[i].add(nd);
                        extentIndex.ajouterNoeud(nd);

                        if (nd.getContent().getIntent().equals(intent)) {
                            treillis.setTop(treillis.findTop());
                            return;
                        }
                    } else { // ancienne paire
                        Intent itn = (nd.getContent().getIntent())
                                .intentIntersection(intent);

                        if (isAGenerator(itn, li2)) { // si nd est un
                                                        // générateur
                            LatticeNodeNR newNoeud = new LatticeNodeNR(
                                                                       new ConceptImp(
                                                                                      nd
                                                                                              .getContent()
                                                                                              .getExtent()
                                                                                              .extentUnion(
                                                                                                           extent),
                                                                                      itn));
                            newNoeud.getContent().getExtent().add(objet);
                            extentIndex.ajouterNoeud(newNoeud);
                            treillis.add(newNoeud);
                            treillis.incNbOfNodes();
                            li2[itn.size()].add(newNoeud);

                            if (itn.equals(intent)) {
                                treillis.setTop(treillis.findTop());
                                return;
                            }
                        } // fin if
                    } // fin else
                } // fin for
            treillis.setTop(treillis.findTop());
        } // fin else
    } // fin doGodin

    // ******************************************
    // METHODES AUXILLAIRES:
    // ******************************************

    // Trouver une extension dans un ensemble
    private boolean trouver(Vector v, Extent e) {
        return v.contains(e);
    }

    private class ExtentIndex {
        private Vector[] ei;

        protected ExtentIndex() {
            ei = new Vector[br.getObjectsNumber() + 1];
            for (int i = 0; i < ei.length; i++)
                ei[i] = new Vector();
        }

        protected void ajouterNoeud(LatticeNodeNR n) {
            ei[n.getContent().getExtent().size()].add(n);
        }

        protected LatticeNodeNR trouverNoeudCandidat(Extent e) {
            for (int i = 0; i < ei[e.size()].size(); i++) {
                LatticeNodeNR lnr = (LatticeNodeNR) ei[e.size()].elementAt(i);
                if (lnr.getContent().getExtent().equals(e))
                    return lnr;
            }
            return null;
        }

        protected int size() {
            return ei.length;
        }

        protected Vector getAt(int i) {
            return ei[i];
        }

        protected void effacerNoeud(LatticeNodeNR n) {
            ei[n.getContent().getExtent().size()].remove(n);
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.algorithm.LatticeAlgorithmInc#addConcept(lattice.util.ConceptImp)
     */
    public void addConcept(Concept c) {
        // TODO Auto-generated method stub

    }
} // fin classe
