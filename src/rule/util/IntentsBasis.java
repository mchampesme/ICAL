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

/*
 * Created on 2004-09-02
 * @author Manuel Aupetit
 */
package rule.util;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import lattice.alpha.util.BGIntent;
import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.ConceptNode;

/**
 * A temporary class to modelise an intent basis, in order to test the intents visualization
 * @author Manuel Aupetit
 */
public class IntentsBasis {

	protected CompleteConceptLattice lattice = null;
	protected List<IntentInstance> intents = null;
	protected double minSupport = 0.0;
	protected double maxSupport = 1.0;
	
	public IntentsBasis(CompleteConceptLattice lattice) {
		this.lattice = lattice;
		setIntents();
	}
	
	public IntentsBasis(CompleteConceptLattice lattice, List<IntentInstance> intents, double minSupport, double maxSupport) {
		this.lattice = lattice;
		this.intents = intents;
		this.minSupport = minSupport;
		this.maxSupport = maxSupport;
	}
	
	
	/**
	 * This method creates a factice set of intents from the lattice,
	 * these intents are used to test the visualization code.
	 */
	public void setIntents() {
		this.intents = new Vector();
		this.minSupport = 1.0;
		this.maxSupport = 0.0;
		
		lattice.getTop().resetDegre();
		int nextIdNode = 0;
		Vector Q = new Vector();
		Q.add(lattice.getTop());
		ConceptNode node;
		int maxExtentSize = ((ConceptNode)Q.get(0)).getContent().getExtent().size();
		
		while (Q.size() != 0) {
			node = (ConceptNode) Q.remove(0);

			Intent currentIntent = new BGIntent();
			for (FormalAttribute attr : node.getContent().getIntent()) {
				currentIntent.add(attr);
			}
			
			double support = ((int) (100 * node.getContent().getExtent().size() / maxExtentSize)) / 100.0;
			if (support < minSupport) {
				minSupport = support;
			}
			if (support > maxSupport) {
				maxSupport = support;
			}
			
			if (!currentIntent.isEmpty()) {
				this.intents.add(new IntentInstance(currentIntent, support));
			}
			
			for (Iterator it = node.getChildren().iterator(); it.hasNext(); ) {
				ConceptNode P = (ConceptNode) it.next();
				if (P.getDegre() == -1) {
					P.setDegre(P.getParents().size());
				}
				P.setDegre(P.getDegre() - 1);
				if (P.getDegre() == 0) {
					Q.add(P);
				}
			}
		}
	}
	
	public CompleteConceptLattice getLattice() {
		return this.lattice;
	}

	public String getLatticeDescription() {
		return this.lattice.getDescription();
	}
	
	public List<IntentInstance> getIntents() {
		return this.intents;
	}
	
	public double getMinSupport() {
		return this.minSupport;
	}
	
	public double getMaxSupport() {
		return this.maxSupport;
	}
	
	public Intent getAttributes() {
		return intents.get(intents.size() - 1).getIntent();
	}

	public IntentsBasis filterIntentsByAttributes(Intent discardedAttributes) {
		List<IntentInstance> newIntents = new ArrayList<IntentInstance>(intents);
		Iterator<IntentInstance> intentsIter = newIntents.iterator();
		while (intentsIter.hasNext()) {
			IntentInstance intentInstance = intentsIter.next();
			for (FormalAttribute attr : discardedAttributes) {
				if (intentInstance.getIntent().contains(attr)) {
					intentsIter.remove();
					break;
				}
			}
		}
		return new IntentsBasis(this.lattice, newIntents, this.minSupport,
				this.maxSupport);
	}

	
	public IntentsBasis filterIntentsBySupport(double minSupport, double maxSupport) {
		List<IntentInstance> newIntents = new ArrayList<IntentInstance>(intents);
		Iterator<IntentInstance> intentsIter = newIntents.iterator();
		while (intentsIter.hasNext()) {
			IntentInstance intentInstance = intentsIter.next();
			double support = intentInstance.getSupport();
			if (support < minSupport || support > maxSupport) {
				intentsIter.remove();
			}
		}
		return new IntentsBasis(this.lattice, newIntents, minSupport, maxSupport);
	}

}
