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
 * Created on 28-Apr-2004
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package lattice.algorithm.rca;

import java.util.Vector;

import lattice.gui.MultiFCASettingsView;
import lattice.gui.graph.LatticeGraphFrame;
import lattice.iceberg.algorithm.BordatIceberg;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.ConceptNodeImp;

/**
 * @author rouanehm (Amine Mohamed ROUANE-HACENE)
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */

public class LatticeFamily {
	// contexts in rcf are not necessary all involved in the Multi-FCA process
	// that's why we stated the following variable
	Vector workingRCF;
	RelationalContextFamily fullRCF;
		 
	// the selected Object-Valued-Attribute set
	Vector workingOVASet;
 	
	public LatticeFamily(RelationalContextFamily fullRCF){
	this.fullRCF =fullRCF; 
	workingRCF = new Vector();	
	
	// compose the effective RCF
	//put the selected initial context at the beginning of the vector
	workingRCF.add(fullRCF.getForName((String) MultiFCASettingsView.getSelectedInitalContext()));
	for(int i=0;i<MultiFCASettingsView.getSelectedContexts().size();i++){	
		String selectedCtx = MultiFCASettingsView.getSelectedContexts().elementAt(i).toString();
		if(selectedCtx.compareTo((String)MultiFCASettingsView.getSelectedInitalContext())!=0)
		workingRCF.add(fullRCF.getForName(selectedCtx));
	}
	workingOVASet = new Vector();
	for(int i=0;i<MultiFCASettingsView.getSelectedRelAttributes().size();i++)
	workingOVASet.add(fullRCF.getForName(MultiFCASettingsView.getSelectedRelAttributes().elementAt(i).toString()));	
	} //constructor

	public Vector getWorkingContextSet(){
		return workingRCF;
	}
	public Vector getWorkingOVASet(){
		 return workingOVASet;
	}
	
	public void computeInitialLatticeGraphs() {
		for(int i=0;i<workingRCF.size();i++){ 
			RelationBuilder absRel=(RelationBuilder) workingRCF.elementAt(i);
			if(absRel instanceof MatrixBinaryRelationBuilder) reConstructLattice((MatrixBinaryRelationBuilder)absRel);
			//absRel.getLattice().fillSimplified();
		}			
	}	
	
	public void reConstructLatticeFamily(){
			for(int i=0;i<workingRCF.size();i++){ 
				RelationBuilder absRel=(RelationBuilder) workingRCF.elementAt(i);
				if(absRel instanceof MatrixBinaryRelationBuilder) reConstructLattice((MatrixBinaryRelationBuilder) absRel);
			}	
		}
		public static void reConstructLattice(MatrixBinaryRelationBuilder ctx){
			//an alternative could be the use of AlgoTask
			BordatIceberg algo=new BordatIceberg(ctx);
			algo.doAlgorithm(); 		
			//ValtchevEtAl2 algo= new ValtchevEtAl2(rel);
			//algo.doAlgorithm();
			CompleteConceptLattice lattice=algo.getLattice();
			ctx.setLattice(lattice);
			lattice.setDescription("Initial lattice of context: "+ctx.getName());
			// display the resulting lattice
			//lattice.fillSimplified();
			ConceptNodeImp.resetNodeId();
			LatticeGraphFrame f = new LatticeGraphFrame(lattice.getDescription(), lattice.getTop());
			f.show();
			// if we want to use GSH for the scaling of OVA, here is the code:
			//CERES anAlgo=new CERES(ctx);
			//anAlgo.doAlgorithm();
			//ctx.setLattice(anAlgo.getLattice());
		}

		/**
		 * @param i context index
		 * @return the corresponding context in RCF 
		 */
		public RelationBuilder getWorkingContext(int i) {
			return (RelationBuilder) workingRCF.elementAt(i);
		}
		
		public RelationBuilder getWorkingContext(String contextName){
			for(int i=0;i< workingRCF.size();i++){
				RelationBuilder current = (RelationBuilder) workingRCF.elementAt(i);
				if(current.getName().compareTo(contextName)==0) 
				return current;
			}
			return null;
		}

	public InterObjectBinaryRelation getWorkingOVA(int i) {
		return (InterObjectBinaryRelation) workingOVASet.elementAt(i); 
	}
		/**
	 	* @param ovaName
	 	* @return relational attribute context
	 	*/
		public InterObjectBinaryRelation getWorkingOVA(String ovaName) {
			for(int i=0;i< workingOVASet.size();i++){
				InterObjectBinaryRelation current = (InterObjectBinaryRelation) workingOVASet.elementAt(i);
				if(current.getName().compareTo(ovaName)==0) 
				return current;
			}			
			return null;
		}		
		
		/**
		 * @param ctx
		 * @return the set of object-valued attributes in the context ctx 
		 * (as InterObjectBinaryRelation array)
		 */
		public Vector getOVASet(RelationBuilder ctx) {
			Vector result=new Vector(0);
			for(int i=0;i<workingOVASet.size();i++){
				InterObjectBinaryRelation rel=(InterObjectBinaryRelation) workingOVASet.elementAt(i);
				// check object context of given OVA context
				String currentCtx = rel.getObjectsContextName(); 
				if(currentCtx.compareTo(ctx.getName())==0)	
				result.add(rel);
			}
			return result;
		}

		/**
		 * @param relation
		 */
		public void addContextToRCF(MatrixBinaryRelationBuilder ctx) {
			workingRCF.add(ctx);			
		}

		/**
		 * @param ctx
		 */
		public void removeContext(RelationBuilder ctx) {
			workingRCF.remove(ctx);			
		}

		/**
		 * 
		 */
		public void displayFinalLattices() {			
			MatrixBinaryRelationBuilder binCtx=null;
			// compose lost working RCF
			workingRCF.removeAllElements();
			workingRCF.add(fullRCF.getForName((String) MultiFCASettingsView.getSelectedInitalContext()));
			for(int i=0;i<MultiFCASettingsView.getSelectedContexts().size();i++){	
				String selectedCtx = MultiFCASettingsView.getSelectedContexts().elementAt(i).toString();
				if(selectedCtx.compareTo((String)MultiFCASettingsView.getSelectedInitalContext())!=0)
				workingRCF.add(fullRCF.getForName(selectedCtx));
			}			
			// process labeling according to user settings
			for(int i=0;i<workingRCF.size();i++){ 
				RelationBuilder absRel=(RelationBuilder) workingRCF.elementAt(i);
				if(absRel instanceof MatrixBinaryRelationBuilder) binCtx=(MatrixBinaryRelationBuilder)absRel;
				if(binCtx!=null) {
					//LatticeGraphFrame f0 = new LatticeGraphFrame("Lattice of "+binCtx.getRelationName()+" before processing labels",binCtx.getLattice().getTopConceptNode());
					//f0.show();
					// reduce relational labeling if asked
					if(MultiFCASettingsView.getSelectedRelationalLabeling()==MultiFCASettingsView.getReducedRelationalLabeling())
						RelationalLattice.removeRedundantLinks(fullRCF,binCtx);
					//LatticeGraphFrame f1 = new LatticeGraphFrame("Lattice of "+binCtx.getRelationName()+" lattice after removing redundant links",binCtx.getLattice().getTopConceptNode());
					//f1.show();
					// reduce fundamental labeling is asked
					if(MultiFCASettingsView.getSelectedfundamentalLabeling()==MultiFCASettingsView.getReducedFundamentalLabeling())
					{
						//binCtx.getLattice().fillSimplified();
						//LatticeGraphFrame f2 = new LatticeGraphFrame("Lattice of "+binCtx.getRelationName()+" lattice after filling simplified fields...",binCtx.getLattice().getTopConceptNode());
						//f2.show();
						//RelationalLattice.copySimplified(binCtx.getLattice());
						//LatticeGraphFrame f3 = new LatticeGraphFrame("Lattice of "+binCtx.getRelationName()+" lattice after transfering simplified fields to the original ones...",binCtx.getLattice().getTopConceptNode());
						//f3.show();
						
					}
					//LatticeGraphFrame f = new LatticeGraphFrame("Final Lattice of "+binCtx.getRelationName(),binCtx.getLattice().getTopConceptNode());
					//f.show();
					}
			}//
			for(int i=0;i<workingRCF.size();i++){ 
				RelationBuilder absRel=(RelationBuilder) workingRCF.elementAt(i);
				if(absRel instanceof MatrixBinaryRelationBuilder) binCtx=(MatrixBinaryRelationBuilder)absRel;
				if(binCtx!=null) {					
					LatticeGraphFrame f = new LatticeGraphFrame("Final Lattice of context: "+binCtx.getName(),binCtx.getLattice().getTop());
					f.show();
				}
				}
			}	
}
