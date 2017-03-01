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

import java.util.Collection;
import java.util.Iterator;

import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLatticeImp;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
/**
 * <p>Title: </p>
 * <p>Description: </p>
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: </p>
 * @author unascribed
 * @version 1.0
 */

public abstract class AbstractGodinAlgorithm extends LatticeAlgorithmInc
{
    
    
    /**
     *
     */
    public AbstractGodinAlgorithm() {
    }
    
    /**
     *
     */
    public AbstractGodinAlgorithm(MatrixBinaryRelationBuilder br) {
		super(br);
    }
    
    /**
     * Add a collection of concepts to the lattice. (Godin)
     * @param c
	 */
    public abstract void addConcept(Concept c);
    
    public void doAlgorithm() {
	ConceptNodeImp.resetNodeId();
	long time = System.currentTimeMillis(); // TIMER
	addAll_Godin(getBinaryRelation().getInitialObjectPreConcept(MatrixBinaryRelationBuilder.NO_SORT)); 
    getBinaryRelation().setLattice(getLattice());
	System.out.println("FIN " + (System.currentTimeMillis() - time) + " mSec.\n"); // fin TIMER
    }
    
    public void addAll_Godin(Collection coll) {
	//		int i = 0;
	//		long start, stop;
	//		long total = 0;
	
	// --- Gestion de la progression
		int maxClass=coll.size();
		int nbClass = 0;
		// --- Fin Gestion de la progression
		
		for (Iterator iter = coll.iterator(); iter.hasNext();) {
			//start = System.currentTimeMillis();
			addConcept((ConceptImp) iter.next());
			//stop = System.currentTimeMillis();
			//total = total + (stop - start);

//			i = i + 1;
//			if (i % 100 == 0) {
//				System.out.println(
//					"total Godin sans filtre pour "
//						+ i
//						+ " transactions = "
//						+ total
//						+ "ms"
//						+ "   (size = "
//						+ getLattice().get_nbr_concept()
//						+ ")");
//				total = 0;
//			}

			// --- Gestion de la progression
			nbClass++;
			sendJobPercentage(nbClass*100/maxClass);
			// --- Fin Gestion de la progression

		} 
	}

	/**
	 * Init the first concept
	 */
	public void initFirst(Concept concept) {
		ConceptNode n = new ConceptNodeImp(concept);
		getLattice().setTop(n);
		getLattice().setBottom(n);
		getLattice().initialiseIntentLevelIndex(concept.getIntent().size() + 1);
		getLattice().set_max_transaction_size(concept.getIntent().size());
		getLattice().add(getLattice().getBottom());
		getLattice().incNbOfNodes();
	}

}
