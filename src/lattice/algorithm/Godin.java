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

import java.util.Vector;

import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Intent;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLatticeImp;
import lattice.util.structure.ConceptNodeImp;
/*
import lattice.util.BinaryRelation;
import lattice.util.ConceptImp;
import lattice.util.Intent;
import lattice.util.LatticeNode;
*/
/**
 *
 * <p>Titre : Lattice</p>
 * <p>Description : Manipulation des treillis</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : Université de Montréal</p>
 * @author Alexandre Frantz et Pascal Camarda
 * @version 1.0
 */
public class Godin extends AbstractGodinAlgorithm{

	/**
	 *
	 */
	public Godin(MatrixBinaryRelationBuilder br) {
		super(br);
	}

/**
	 * algorithme de Godin
	 * @param concept
	 */
	public void addConcept(Concept concept) {
		if (getLattice().getBottom() == null)
			initFirst(concept);

		else {
			adjustBottom((CompleteConceptLatticeImp)getLattice(),concept);
			boolean isModified;
			int max_intent_card = getLattice().getIntentLevelIndex().size();
			int nbr_element;
			Intent new_intent;
			Concept new_concept;
			ConceptNodeImp current_node, new_node;
			Vector vector;
			Vector[] temp = new Vector[concept.getIntent().size() + 1];
			initialiseArray(temp);

			for (int i = 0; i < max_intent_card; i++) {
				//Treat each concept in ascending cardinality order.
				vector =
					(Vector) getLattice().getIntentLevelIndex().get(i);
				nbr_element = vector.size();

				for (int j = 0; j < nbr_element; j++) {
					//current_node = (LatticeNode)
					//        ((Vector)intent_level_index.elementAt(i)).elementAt(j);
					current_node = (ConceptNodeImp) vector.elementAt(j);
					new_intent =
						current_node.concept.getIntent().intentIntersection(
							concept.getIntent());
					// modifié
					if (new_intent.size()
						== current_node.concept.getIntent().size()) {
						current_node.concept.getExtent().addAll(
							concept.getExtent());
						temp[i].add(current_node);
						if (current_node
							.concept
							.getIntent()
							.equals(concept.getIntent())) {
							getLattice().setTop(getLattice().findTop());
							return;
						}
					}
					// old pair 
					else {
						// current_node is a generator.
						if (isAGenerator(new_intent, temp)) {
							new_concept =
								new ConceptImp(
									current_node.concept.getExtent().extentUnion(
										concept.getExtent()),
									new_intent);
							new_node = new ConceptNodeImp(new_concept);
							getLattice().add(new_node);
							temp[new_intent.size()].add(new_node);
							modifyEdges(
								current_node,
								new_node,
								temp);
							getLattice().incNbOfNodes();
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
	
	public String getDescription(){
		return "Godin incremental lattice update"; 
	}

} // fin de la classe