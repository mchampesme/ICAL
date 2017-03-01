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
 * Created on 19 déc. 2003
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package lattice.gui.controller;

import java.awt.event.ActionEvent;

import javax.swing.JMenu;

import lattice.algorithm.rca.MultiFCA;
import lattice.algorithm.task.LatticeAlgorithmTask;
import lattice.gui.MultiFCASettingsView;
import lattice.gui.RCAView;
import lattice.gui.RelationalContextEditor;
import lattice.gui.UMLBatchSettingsView;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.RelationalContextFamily;
/**
 * @author rouanehm (Amine Mohamed ROUANE-HACENE)
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class RCAController extends AbstractController {

	private RCAView rcaView;
	private LatticeAlgorithmTask theTask=null;
		
	public RCAController(RelationalContextEditor rce) {
		super(rce);
		rcaView = new RCAView(this);
		rcaView.initMenu();
		theTask=new LatticeAlgorithmTask(rce);
	}
		
	public JMenu getMainMenu(){
		return rcaView.getMainMenu();
	}

	// Multi-FCA algorithm using a complete Lattice (CL) encoding
	public void MultiFCAGeneral(){
		rce.addMessage("Multi-FCA settings input...\n");	
		// Retrieve MultiFCA algorithm parameters
		MultiFCASettingsView.getSettings(rce.getFamilyContexts(),rce);
		if(MultiFCASettingsView.getExitStatus()==MultiFCASettingsView.getTerminatedStatus()) {	
			MultiFCASettingsView.displayRCFSettings();
			MultiFCASettingsView.displayEncodingSettings();
			MultiFCASettingsView.displayLabelingSettings();
			//System.exit(1);
			rce.addMessage("Instanciating Multi-FCA object...\n");
			MultiFCA multiFCA = new MultiFCA(this);
			rce.addMessage("Running Multi-FCA algorithm...\n");
			multiFCA.run();			
			rce.addMessage("Multi-FCA algorithm results ready...\n");
		}
	}

	public void MultiFCAUML() {
	// use predefined UML-RCF settings
		if(MultiFCASettingsView.checkUMLFormat(rce.getFamilyContexts())) {			
		MultiFCASettingsView.useUMLSettings();	
		UMLBatchSettingsView.getSettings(rce);
		if(UMLBatchSettingsView.getExitStatus()==UMLBatchSettingsView.getTerminatedStatus()) 
		{
			MultiFCASettingsView.setEncodingStructure(UMLBatchSettingsView.getEncodingStructure());
			MultiFCASettingsView.setEncodingSchema(UMLBatchSettingsView.getEncodingSchema());
			MultiFCASettingsView.setFundamentalLabeling(UMLBatchSettingsView.getFundamentalLabeling());
			MultiFCASettingsView.setRelationalLabeling(UMLBatchSettingsView.getRelationalLabeling());
			MultiFCASettingsView.displayRCFSettings();
			MultiFCASettingsView.displayEncodingSettings();
			MultiFCASettingsView.displayLabelingSettings();
			//System.exit(1);
			MultiFCA multiFCA = new MultiFCA(this);	
			rce.addMessage("Running Multi-FCA algorithm...\n");
			multiFCA.run();			
			rce.addMessage("Multi-FCA algorithm results ready...\n");
		}
		}
		else
		rce.addMessage("RCF does not fit UML predefined mapping...\n");
	}
	
	
	public RelationalContextFamily getRCF(){
		return rce.getFamilyContexts();
	}
	
	public void addContextToRCF(MatrixBinaryRelationBuilder ctx){	
		rce.addBinaryRelation((MatrixBinaryRelationBuilder) ctx);
	}
//	protected void execAlgorithm(LatticeAlgorithm algo){
//		theTask.setAlgo(algo);
//		theTask.exec();
//	}

	public void checkPossibleActions(){
		rcaView.checkPossibleActions();
		return;
 	}

	public void actionPerformed(ActionEvent arg0) {
		// TODO Auto-generated method stub
		
	}
	public void sendConsoleMessage(String message) {
		rce.addMessage(message);
	}
}