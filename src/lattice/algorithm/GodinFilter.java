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

import java.util.Hashtable;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLatticeImp;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
import lattice.util.structure.Node;

/**
 * <p>
 * Titre : Lattice
 * </p>
 * <p>
 * Description : Manipulation des treillis
 * </p>
 * <p>
 * Copyright : Copyright (c) 2002
 * </p>
 * <p>
 * Société : Université de Montréal
 * </p>
 * 
 * @author Alexandre Frantz et Pascal Camarda
 * @version 1.0
 */
public class GodinFilter extends AbstractGodinAlgorithm {
    private Map<FormalAttribute, Node<Concept>> item_index;

    /**
     *
     */
    public GodinFilter(MatrixBinaryRelationBuilder br) {
        super(br);
        item_index = new Hashtable<FormalAttribute, Node<Concept>>();
    }

    /**
     * @param concept
     * @return selected_nodes
     */
    protected Vector selectAndClassify(Concept concept) {
        Node<Concept> node_item;
        Vector selected_nodes = new Vector();
        initialiseVector(selected_nodes, getBinaryRelation()
                .getAttributesNumber() + 1);
        // getLattice().get_max_transaction_size() + 2);

        adjustTop(concept, selected_nodes);

        for (FormalAttribute attr : concept.getIntent()) {
            node_item = item_index.get(attr);
            search(node_item, selected_nodes);
        }

        ((Vector) selected_nodes.lastElement()).add(getLattice().getBottom());
        // .add(bottom);//***
        cleanNodes(selected_nodes);
        return selected_nodes;
    }

    /**
     * Sert a maintenir le Top dans l'algorithme Godin 2
     * 
     * @param concept
     * @param selected_nodes
     */
    protected void adjustTop(Concept concept, Vector selected_nodes) {
        if (!getLattice().getTop().getContent().getIntent().isEmpty()) {
            Intent top_intent_intersection = getLattice().getTop().getContent()
                    .getIntent().intentIntersection(concept.getIntent());
            if (top_intent_intersection.isEmpty()) {
                Node<Concept> temp_node = getLattice().getTop();
                getLattice()
                        .setTop(
                                new ConceptNodeImp(
                                                   new ConceptImp(
                                                                  concept
                                                                          .getExtent()
                                                                          .extentUnion(
                                                                                       temp_node
                                                                                               .getContent()
                                                                                               .getExtent()),
                                                                  top_intent_intersection)));
                temp_node.getParents().add(getLattice().getTop());
                getLattice().add(getLattice().getTop());
                getLattice().incNbOfNodes();
                ((Vector) selected_nodes.firstElement()).add(getLattice()
                        .getTop());
            }
        }
        // top is a modified node
        else {
            ((Vector) selected_nodes.firstElement()).add(getLattice().getTop());
        }
    }

    /**
     * @param node
     * @param selected_nodes
     */
    protected void search(Node<Concept> node, Vector selected_nodes) {
        Node<Concept> node_temp;
        if (!node.getVisited()) {
            ((Vector) selected_nodes.elementAt(node.getContent().getIntent()
                    .size())).add(node);
            node.setVisited(true);
        }

        Iterator it = node.getChildren().iterator();
        while (it.hasNext()) {
            node_temp = (Node<Concept>) it.next();
            if (!node_temp.getVisited()) {
                search(node_temp, selected_nodes);
            }
        }
    }

    /**
     * @param selected_nodes
     */
    protected void cleanNodes(Vector selected_nodes) {
        Vector vector;

        for (int i = 0; i < selected_nodes.size(); i++) {
            vector = ((Vector) selected_nodes.elementAt(i));
            for (int j = 0; j < vector.size(); j++) {
                ((ConceptNodeImp) vector.elementAt(j)).visited = false;
            }
        }
        getLattice().getBottom().setVisited(true);
    }

    /**
     * Add a new concept to the lattice
     * 
     * @param concept
     */
    public void addConcept(Concept concept) {
        if (getLattice().getBottom() == null)
            initFirst(concept);

        else {
            adjustBottom((CompleteConceptLatticeImp) getLattice(), concept);
            Vector selected_nodes = selectAndClassify(concept);

            boolean isModified;
            Intent new_intent;
            Concept new_concept;
            Node<Concept> current_node, new_node;
            Intent intent_index = (Intent) concept.getIntent().clone();
            // for Index update.

            Vector vector;
            Vector[] temp = new Vector[concept.getIntent().size() + 1];
            initialiseArray(temp);

            // Treat each concept in ascending cardinality order.
            for (int i = 0; i < selected_nodes.size(); i++) {
                vector = (Vector) selected_nodes.elementAt(i);
                for (int j = 0; j < vector.size(); j++) {
                    current_node = (ConceptNodeImp) vector.elementAt(j);
                    new_intent = current_node.getContent().getIntent()
                            .intentIntersection(concept.getIntent());

                    // concept modifié
                    if (new_intent.size() == current_node.getContent()
                            .getIntent().size()) {
                        current_node.getContent().getExtent()
                                .addAll(concept.getExtent());
                        temp[i].add(current_node);

                        // mise a jour de la table d'indexes.
                        if (!intent_index.isEmpty())
                            intent_index.removeAll(new_intent);

                        if (current_node.getContent().getIntent()
                                .equals(concept.getIntent())) {
                            getLattice().setTop(getLattice().findTop());
                            return;
                        }
                    }

                    // old pair
                    else {
                        // current_node is a generator.
                        if (isAGenerator(new_intent, temp)) {
                            new_concept = new ConceptImp(current_node
                                    .getContent().getExtent()
                                    .extentUnion(concept.getExtent()),
                                                         new_intent);
                            new_node = new ConceptNodeImp(new_concept);
                            getLattice().add(new_node);
                            temp[new_intent.size()].add(new_node);
                            modifyEdges(current_node, new_node, temp);
                            getLattice().incNbOfNodes();

                            // adjust the item index.
                            if (!intent_index.isEmpty()) {
                                Intent intent = new_intent
                                        .intentIntersection(intent_index);
                                for (FormalAttribute attr : intent) {
                                    item_index.put(attr, new_node);
                                }
                                intent_index.removeAll(intent);
                            }

                            if (new_intent.equals(concept.getIntent())) {
                                getLattice().setTop(getLattice().findTop());
                                return;
                            }
                        }
                    }
                }
            }
            getLattice().setTop(getLattice().findTop());
        }
    }

    public String getDescription() {
        return "Godin Filter incremental lattice update";
    }

} // fin de la classe LatticeAlgorithmGodinFilter
