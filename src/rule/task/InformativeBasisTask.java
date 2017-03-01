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
package rule.task;

import lattice.algorithm.LatticeAlgorithm;
import lattice.gui.RelationalContextEditor;
import lattice.gui.tooltask.WaitingStepTaskFrame;
import lattice.iceberg.algorithm.BordatIceberg;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import rule.algorithm.InformativeBasis;
import rule.generator.Jen;
import rule.gui.TableVisualization;
import rule.util.RulesBasis;

/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class InformativeBasisTask extends ruleAbstractTask {

	private double minConfiance = 50.0/100.0;
	private double minSupportPercentage = 0.05;
	
	private String nomFichierEntre;
	private String nomFichierSauvegardeExact;
	private String nomFichierSauvegardeApprox;

	
	//	Constructeur
	 public InformativeBasisTask(RelationalContextEditor rce) {
		 this.rce = rce;
	 }

	/* (non-Javadoc)
	 * @see lattice.util.tooltask.JobObservable#getDescription()
	 */
	public String getDescription() {
		return "Informative basis";
	}

	
	public void exec(){
		goodEnded=false;
		InformativeBasisTask newTask=(InformativeBasisTask)clone();
		newTask.taskObserver = new WaitingStepTaskFrame(newTask,3,rce.getConsole());
	}

	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {

		double minSupportPercentage = 0.05;
		LatticeAlgorithm algo = new BordatIceberg( (MatrixBinaryRelationBuilder)rce.getSelectedRelation(), minSupportPercentage );
		rce.addMessage("Processing "+algo.getDescription()+" on the binary relation \""+ ((MatrixBinaryRelationBuilder)rce.getSelectedRelation()).getName()+"\"");
		algo.setJobObserver(taskObserver);
		taskObserver.setTitle(getDescription()+" Running BordatIceberg Algo.");
		algo.run();
		taskObserver.jobEnd(true);
		
		// Lancement de l'algorithme Jen : construction des g»n»rateurs
		Jen algoJen = new Jen( algo.getLattice() );
		algoJen.setJobObserver(taskObserver);
		taskObserver.setTitle(getDescription()+" Processing Jen Algo.");
		algoJen.run();
		taskObserver.jobEnd(true);
    		

		// Construction de la base g»n»rique
		InformativeBasis baseInformative = new InformativeBasis(algo.getLattice(), minConfiance);
		baseInformative.setJobObserver(taskObserver);
		taskObserver.setTitle(getDescription()+" Processing Base Informative Algo.");
		baseInformative.run();
		taskObserver.jobEnd(true);

		new TableVisualization(new RulesBasis(rce.getSelectedRelation(), baseInformative.getBase(), minSupportPercentage, minConfiance), rce);

		taskObserver.taskEnd();
		goodEnded=true;
		
		stringResult=baseInformative.getResultat();
		
		rce.showTaskResult(this);
	}
	

	public void setMinSupport(double minSupport){
	  this.minSupportPercentage=minSupport;
	}
	public void setMinConfiance(double minConfiance){
	  this.minConfiance=minConfiance;
	}
	public void setNomFichierEntre(String nomFichierEntre){
	  this.nomFichierEntre=nomFichierEntre;
	}
	public void setNomFichierSauvegardeApprox(String nomFichierSauvegardeApprox){
	  this.nomFichierSauvegardeApprox=nomFichierSauvegardeApprox;
	}
	public double getMinSupport(){
	  return this.minSupportPercentage;
	}
	public double getMinConfiance(){
	  return this.minConfiance;
	}
	public String getNomFichierEntre(){
	  return this.nomFichierEntre;
	}
	public String getNomFichierSauvegardeApprox(){
	  return this.nomFichierSauvegardeApprox;
	}
	
	public Object clone(){
		InformativeBasisTask newTask=new InformativeBasisTask(rce);
		newTask.theBinRelOnUse=theBinRelOnUse;
		newTask.goodEnded=goodEnded;
		newTask.taskObserver=taskObserver;
		
		// Local values
		newTask.minSupportPercentage=this.minSupportPercentage;
		newTask.minConfiance = this.minConfiance;
		newTask.nomFichierEntre=this.nomFichierEntre;
		newTask.nomFichierSauvegardeExact=this.nomFichierSauvegardeExact;
		newTask.nomFichierSauvegardeApprox=this.nomFichierSauvegardeApprox;
		return newTask;
	}

}
