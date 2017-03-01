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
 * Created on 12 juil. 2003
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package lattice.gui.controller;

import java.awt.event.ActionEvent;
import java.util.Hashtable;
import java.util.Vector;

import javax.swing.JMenu;
import javax.swing.JMenuItem;

import lattice.algorithm.LatticeAlgorithm;
import lattice.algorithm.task.LatticeAlgorithmTask;
import lattice.gsh.algorithm.CERES;
import lattice.gsh.algorithm.Gagci_NoInc;
import lattice.gui.RelationalContextEditor;
import lattice.gui.dialog.Gagci_NoInc_Param;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.relation.ScalingBinaryRelation;
import lattice.util.structure.LatticeGraph;

/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class GSHController extends AbstractController {

	// Le menu et sous menu Algorithms
	private JMenu menuShg = null;	
	private JMenuItem algoCeres = null;
	private JMenuItem algoAresCons = null;
	private JMenuItem algoGodinShg = null;
	private JMenu menuOp;
	private JMenuItem algoAres = null;
	private JMenuItem algoAresDual = null;
	private JMenu menuIcg;
	private JMenuItem algoGagci = null;
	private JMenuItem umlApplication = null;
	private JMenuItem algoGagciNoInc = null;

	private LatticeAlgorithmTask theTask=null;

	/**
	 * 
	 */
	public GSHController(RelationalContextEditor rce) {
		super(rce);
		initMenu();
		theTask=new LatticeAlgorithmTask(rce);
	}
	
	public void initMenu(){
		
		menuShg = new JMenu("Galois Sub-Hierarchy");
		menuShg.setMnemonic('G');

		algoCeres = new JMenuItem("CERES");
		algoCeres.setMnemonic('C');
		algoCeres.addActionListener(this);
		menuShg.add(algoCeres);
				
		algoAresCons = new JMenuItem("ARES Iterative Construction");
		algoAresCons.setMnemonic('A');
		algoAresCons.addActionListener(this);
		menuShg.add(algoAresCons);

		algoGodinShg = new JMenuItem("Godin SHG");
		algoGodinShg.setMnemonic('G');
		algoGodinShg.addActionListener(this);
		menuShg.add(algoGodinShg);

		menuOp=new JMenu("Maintaining SHG");
		menuOp.setMnemonic('M');
		

		algoAres = new JMenuItem("ARES: Add a Formal Object");
		algoAres.setMnemonic('O');
		algoAres.addActionListener(this);
		menuOp.add(algoAres);

		algoAresDual = new JMenuItem("ARES dual: Add a Formal Attribute");
		algoAresDual.setMnemonic('A');
		algoAresDual.addActionListener(this);
		menuOp.add(algoAresDual);

		menuShg.add(menuOp);

		menuIcg=new JMenu("Iterative Cross Generalization");
		menuIcg.setMnemonic('I');
		
		algoGagci = new JMenuItem("ICG");
		algoGagci.setMnemonic('G');
		algoGagci.addActionListener(this);
		menuIcg.add(algoGagci);
		
		umlApplication = new JMenuItem("UML application: batch ");
		umlApplication.setMnemonic('U');
		umlApplication.addActionListener(this); 
		menuIcg.add(umlApplication);
		
		menuShg.add(menuIcg);

	}
	
	public JMenu getMainMenu(){
		return menuShg;
	}

	/* (non-Javadoc)
	 * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
	 */
	public void actionPerformed(ActionEvent arg0) {
		if(arg0.getSource()==algoCeres){
			execAlgorithm(new CERES((MatrixBinaryRelationBuilder)rce.getSelectedRelation()));
		}
		if(arg0.getSource()==algoAresCons){
            rce.addMessage("This Algorithm AresConstruction is not yet imlemented!\n");
		}
		if(arg0.getSource()==algoGodinShg){
			rce.addMessage("This Algorithm is not yet imlemented!\n");
		}
		if(arg0.getSource()==algoAres){
            rce.addMessage("This Algorithm Ares is not yet imlemented!\n");
		}
		if(arg0.getSource()==algoAresDual){
            rce.addMessage("This Algorithm AresDual is not yet imlemented!\n");
		}
		if(arg0.getSource()==algoGagci){
			execAlgoGagciNoInc();
		}
		if(arg0.getSource()==umlApplication){
			execGagciUmlApplication();
		}
		rce.checkPossibleActions();
	}

	protected void execAlgorithm(LatticeAlgorithm algo){
		rce.setWorkOnRelation(algo.getBinaryRelation()); // marquer la relation 'On Use'
		Vector binRelOnUse=new Vector();
		if(algo instanceof Gagci_NoInc){
			binRelOnUse.addAll(((Gagci_NoInc)algo).getSetOfEnrichingRelations());
			for(int i=0;i<binRelOnUse.size();i++){
				rce.setWorkOnRelation((RelationBuilder)binRelOnUse.elementAt(i)); // marquer la relation 'On Use'
			}
		}else{
			binRelOnUse.add(algo.getBinaryRelation());
		}
		theTask.setBinRelOnUse(binRelOnUse);
		theTask.setAlgo(algo);
		theTask.exec();
	}


	protected void execAlgoGagciNoInc(){
		if(Gagci_NoInc_Param.askParameter(rce.getFamilyContexts(),rce)){
			LatticeAlgorithm algo=new Gagci_NoInc((MatrixBinaryRelationBuilder)Gagci_NoInc_Param.getSetOfKi().elementAt(0),Gagci_NoInc_Param.getSetOfKi(),Gagci_NoInc_Param.getSetOfKiRelation(),Gagci_NoInc_Param.getLesGraphInit(),null);
			execAlgorithm(algo);		
		}
	}

	protected void execGagciUmlApplication(){
		MatrixBinaryRelationBuilder mainKi=null;
		Hashtable mainKiRel=new Hashtable();
		Vector setOfKi=new Vector();
		Vector setOfRel=new Vector();
		Hashtable setOfInitGraph=new Hashtable();
		for(int i=0;i<rce.getFamilyContexts().size();i++){
			if(rce.getFamilyContexts().get(i) instanceof MatrixBinaryRelationBuilder && rce.getFamilyContexts().get(i).getName().equals("Class")){
				mainKi=(MatrixBinaryRelationBuilder)rce.getFamilyContexts().get(i);
				for(int j=0;j<rce.getFamilyContexts().size();j++){
					if(rce.getFamilyContexts().get(j) instanceof InterObjectBinaryRelation){
						if(rce.getFamilyContexts().get(j).getName().equals("isType_at") 
							|| rce.getFamilyContexts().get(j).getName().equals("isTypeDecl_at")
							|| rce.getFamilyContexts().get(j).getName().equals("Own_at")
							) {
								Vector v=(Vector)mainKiRel.get("Attribute");
								if(v==null) {
									v=new Vector();
								} 
								v.addElement(rce.getFamilyContexts().get(j));
								mainKiRel.put("Attribute",v);
							}
						if(rce.getFamilyContexts().get(j).getName().equals("isTypeRet_op") 
							|| rce.getFamilyContexts().get(j).getName().equals("isTypeDecl_op")
							|| rce.getFamilyContexts().get(j).getName().equals("Own_op")
							|| rce.getFamilyContexts().get(j).getName().startsWith("isTypeParam")
							) {
								Vector v=(Vector)mainKiRel.get("Operation");
								if(v==null) {
									v=new Vector();
								} 
								v.addElement(rce.getFamilyContexts().get(j));
								mainKiRel.put("Operation",v);
							}
						if(rce.getFamilyContexts().get(j).getName().equals("isTypeOrig_as") 
							|| rce.getFamilyContexts().get(j).getName().equals("isTypeDest_as")
							|| rce.getFamilyContexts().get(j).getName().equals("isTypeAssoc_as")
							|| rce.getFamilyContexts().get(j).getName().equals("OwnDest_as")
							|| rce.getFamilyContexts().get(j).getName().equals("OwnOrig_as")
							) {
								Vector v=(Vector)mainKiRel.get("Association");
								if(v==null) {
									v=new Vector();
								} 
								v.addElement(rce.getFamilyContexts().get(j));
								mainKiRel.put("Association",v);
							}
					}
				}
			}
			if(rce.getFamilyContexts().get(i) instanceof MatrixBinaryRelationBuilder && rce.getFamilyContexts().get(i).getName().equals("Attribute")){
				setOfKi.addElement(rce.getFamilyContexts().get(i));
				Hashtable lesRels=new Hashtable();
				setOfRel.addElement(lesRels);
				for(int j=0;j<rce.getFamilyContexts().size();j++){
					if(rce.getFamilyContexts().get(j) instanceof InterObjectBinaryRelation){
						if(rce.getFamilyContexts().get(j).getName().equals("hasType_at") 
							|| rce.getFamilyContexts().get(j).getName().equals("hasTypeDecl_at")
							) {
								Vector v=(Vector)lesRels.get("Class");
								if(v==null) {
									v=new Vector();
								} 
								v.addElement(rce.getFamilyContexts().get(j));
								lesRels.put("Class",v);
							}
					}
				}
			}
			if(rce.getFamilyContexts().get(i) instanceof MatrixBinaryRelationBuilder && rce.getFamilyContexts().get(i).getName().equals("Operation")){
				setOfKi.addElement(rce.getFamilyContexts().get(i));
				Hashtable lesRels=new Hashtable();
				setOfRel.addElement(lesRels);
				for(int j=0;j<rce.getFamilyContexts().size();j++){
					if(rce.getFamilyContexts().get(j) instanceof InterObjectBinaryRelation){
						if(rce.getFamilyContexts().get(j).getName().equals("hasTypeRet_op") 
							|| rce.getFamilyContexts().get(j).getName().equals("hasTypeDecl_op")
							|| rce.getFamilyContexts().get(j).getName().startsWith("hasTypeParam")
							) {
								Vector v=(Vector)lesRels.get("Class");
								if(v==null) {
									v=new Vector();
								} 
								v.addElement(rce.getFamilyContexts().get(j));
								lesRels.put("Class",v);
							}
					}
				}
			}
			if(rce.getFamilyContexts().get(i) instanceof MatrixBinaryRelationBuilder && rce.getFamilyContexts().get(i).getName().equals("Association")){
				setOfKi.addElement(rce.getFamilyContexts().get(i));
				Hashtable lesRels=new Hashtable();
				setOfRel.addElement(lesRels);
				for(int j=0;j<rce.getFamilyContexts().size();j++){
					if(rce.getFamilyContexts().get(j) instanceof InterObjectBinaryRelation){
						if(rce.getFamilyContexts().get(j).getName().equals("hasTypeOrig_as") 
							|| rce.getFamilyContexts().get(j).getName().equals("hasTypeDest_as")
							|| rce.getFamilyContexts().get(j).getName().equals("hasTypeAssoc_as")
							) {
								Vector v=(Vector)lesRels.get("Class");
								if(v==null) {
									v=new Vector();
								} 
								v.addElement(rce.getFamilyContexts().get(j));
								lesRels.put("Class",v);
							}
					}
				}
			}
			if(rce.getFamilyContexts().get(i) instanceof MatrixBinaryRelationBuilder && rce.getFamilyContexts().get(i).getName().equals("Class_Inheritance")){
				CERES anAlgo=new CERES((MatrixBinaryRelationBuilder)rce.getFamilyContexts().get(i));
				anAlgo.doAlgorithm();
				setOfInitGraph.put("Class",rce.getFamilyContexts().get(i).getLattice());
			}
		}
		
		setOfKi.addElement(mainKi);
		setOfRel.addElement(mainKiRel);	
		if(mainKiRel.size()==0) rce.addMessage("Invalid Context Family!\n");
		LatticeAlgorithm algo=new Gagci_NoInc(mainKi,setOfKi,setOfRel,setOfInitGraph,rce);
		execAlgorithm(algo);		
	}
	
	public void checkPossibleActions(){

		if(rce.getFamilyContexts().size()==0){
			menuShg.setEnabled(false);
			return;
		}

		RelationBuilder absRel=rce.getSelectedRelation();

		if(absRel instanceof MatrixBinaryRelationBuilder){
			if(rce.isOnWork(absRel)) menuShg.setEnabled(false);
			else {
				menuShg.setEnabled(true);
				if(absRel.getLattice()!=null && absRel.getLattice() instanceof LatticeGraph) {
					algoAres.setEnabled(true);
					algoAresDual.setEnabled(true);
				} else{
					algoAres.setEnabled(false);
					algoAresDual.setEnabled(false);				
				}
			}
		}

		if(absRel instanceof ScalingBinaryRelation){
			menuShg.setEnabled(false);
		}

		if(absRel instanceof InterObjectBinaryRelation){
			menuShg.setEnabled(false);
		}
	}


}
