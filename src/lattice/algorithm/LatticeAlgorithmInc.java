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

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.CompleteConceptLatticeImp;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
// import lattice.util.ConceptImp;
import lattice.util.structure.Node;

/**
 * <p>
 * Titre : Petko&al 2
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
 * @author non attribuable
 * @version 2.0
 */

/*
 * Description : Ajout de quelques méthodes Copyright : Copyright (c) 2004
 * SociÈtÈ :Universite de Montréal @author Mame Awa Diop et Petko Valtchev
 * 
 * @version 1.1
 */

public abstract class LatticeAlgorithmInc extends LatticeAlgorithm {

    /**
     * Le treillis sur lequel l'algo travaille
     */

    public LatticeAlgorithmInc() {
        super();
    }

    public LatticeAlgorithmInc(MatrixBinaryRelationBuilder bRel) {
        super(bRel);
    }

    public abstract void addConcept(Concept c);

    // ------------------------------------------------------
    // Méthodes sortie de CompleteConceptLattice

    public void adjustMaxIntentLevelIndex(CompleteConceptLattice lattice,
                                          Concept concept) {
        int size = lattice.getIntentLevelIndex().size();
        lattice.initialiseIntentLevelIndex(concept.getIntent().size() - size
                                           + 1);
    }

    public void adjustBottom(CompleteConceptLattice lattice, Concept concept) {
        Node<Concept> bottom = lattice.getBottom();
        if (!bottom.getContent().getIntent().containsAll(concept.getIntent())) {
            Intent new_intents = concept.getIntent().clone();
            new_intents.removeAll(bottom.getContent().getIntent());

            if (bottom.getContent().getExtent().isEmpty()) {

                // removeBottomFromIntentLevelIndex(bottom); // wakila a enlever

                bottom.getContent().getIntent().addAll(concept.getIntent());
                // adjustMaxIntentLevelIndex(concept,bottom.getConcept().getIntent().size());
                adjustMaxIntentLevelIndex(lattice, concept);
                // addBottomToIntentLevelIndex(bottom); // wakila a enlever

            }

            else {

                ConceptNodeImp node = new ConceptNodeImp(
                                                         new ConceptImp(
                                                                        new SetExtent(),
                                                                        bottom
                                                                                .getContent()
                                                                                .getIntent()
                                                                                .intentUnion(
                                                                                             concept
                                                                                                     .getIntent())));
                node.parents.add(bottom);
                bottom.getChildren().add(node);
                bottom = node;
                bottom.setVisited(true); // pkoi j'ai fait ca...
                List<List<Node<Concept>>> intentIndex = lattice
                        .getIntentLevelIndex();
                for (int i = intentIndex.size() - 1; i < lattice.getBottom()
                        .getContent().getIntent().size(); i++) {
                    intentIndex.add(new Vector<Node<Concept>>());
                }
                intentIndex.get(intentIndex.size() - 1).add(bottom);
                lattice.addBottomToIntentLevelIndex(bottom);
                lattice.incNbOfNodes();
            }

        }
    }

    public void initialiseArray(Vector[] temp) {
        for (int i = 0; i < temp.length; i++) {
            temp[i] = new Vector(8);
        }
    }

    public Vector[] candidates(ConceptNode current_node, ConceptNode[] psi) {
        ConceptNode candidate;
        Vector[] candidates = new Vector[current_node.getContent().getIntent()
                .size()];
        initialiseArray(candidates);

        for (Iterator i = current_node.getParents().iterator(); i.hasNext();) {
            candidate = psi[((ConceptNodeImp) i.next()).id.intValue()];
            // eviter la redondance.
            if (!candidates[candidate.getContent().getIntent().size()]
                    .contains(candidate)) { // psi.
                candidates[candidate.getContent().getIntent().size()]
                        .add(candidate);
            }
        }
        return candidates;
    }

    public boolean isAGenerator(Intent new_intent, Vector[] temp) {
        int cardinality = new_intent.size();
        int nbr_element = temp[cardinality].size();

        for (int i = 0; i < nbr_element; i++) {
            if (new_intent.equals(((ConceptNodeImp) temp[cardinality]
                    .elementAt(i)).concept.getIntent())) {
                return false;
            }
        }
        return true; // A generator.
    }

    public void modifyEdges(Node<Concept> current_node, Node<Concept> new_node,
                            Vector[] temp) {
        Node<Concept> parent_node;
        boolean parent;
        int nbr_elem;

        current_node.getParents().add(new_node);
        new_node.getChildren().add(current_node);

        for (int k = 0; k < new_node.getContent().getIntent().size(); k++) {
            nbr_elem = temp[k].size();

            for (int l = 0; l < nbr_elem; l++) {
                parent_node = ((Node<Concept>) temp[k].get(l));

                if (new_node.getContent().getIntent()
                        .containsAll(parent_node.getContent().getIntent())) {
                    // parent_node is a potential parent of new_node.

                    parent = true;
                    Iterator iter_children = parent_node.getChildren().iterator();
                    Node<Concept> child;

                    while (iter_children.hasNext()) {
                        child = (Node<Concept>) iter_children.next();

                        if (new_node.getContent().getIntent()
                                .containsAll(child.getContent().getIntent())) {

                            parent = false;
                            break;
                        }
                    }

                    if (parent) {
                        // drop link
                        if (current_node.getParents().contains(parent_node)) {
                            current_node.getParents().remove(parent_node);
                            parent_node.getChildren().remove(current_node);
                        }
                        parent_node.getChildren().add(new_node); // add link
                        new_node.getParents().add(parent_node);
                    }
                }// end if
            }// end for
        }// end for
    }

    public void initialiseVector(Vector vector, int size) {
        for (int i = 0; i < size; i++) {
            vector.add(new Vector());
        }
    }

    public boolean isAModifiedNode(Concept concept, Node<Concept> current_node) {
        boolean isModifiedNode = concept.getIntent()
                .containsAll(current_node.getContent().getIntent());
        return isModifiedNode;
    }

    /**
     * @param conceptDeleted
     */
    public void deleteConcept(Concept conceptDeleted) {
        // TODO Auto-generated method stub

    }

    // --------------------------------------------------------
}