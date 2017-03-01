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

import lattice.algorithm.GodinAD;
import lattice.algorithm.LatticeAlgorithm;
import lattice.gui.RelationalContextEditor;
import lattice.gui.tooltask.WaitingStepTaskFrame;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import rule.algorithm.LuxenburgerBasis;
import rule.gui.TableVisualization;
import rule.util.RulesBasis;

/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class LuxenburgerTask extends ruleAbstractTask {

	private double minSupport = 00.0/100.0;
	private double minConfiance = 50.0/100.0;
	
	
	private String nomFichierEntre;
	private String nomFichierSauvegardeApprox;


	//	Constructeur
	 public LuxenburgerTask(RelationalContextEditor rce) {
		 this.rce = rce;
	 }

	/* (non-Javadoc)
	 * @see lattice.util.tooltask.JobObservable#getDescription()
	 */
	public String getDescription() {
		return "Luxenburger";
	}
	
	public void exec(){
		goodEnded=false;
		LuxenburgerTask newTask=(LuxenburgerTask)clone();
		newTask.taskObserver = new WaitingStepTaskFrame(newTask,2,rce.getConsole());
	}


	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		rce.addMessage("Generating lattice using Godin algorithm on the binary relation \""+ rce.getSelectedRelation().getName()+"\"");
		LatticeAlgorithm algo = new GodinAD( (MatrixBinaryRelationBuilder)rce.getSelectedRelation());			
		algo.setJobObserver(taskObserver);
		taskObserver.setTitle(getDescription()+" Running Godin Algorithm");
		algo.run();
		// Lancement de l'algorithme Luxemburger
		LuxenburgerBasis baseCouv = new LuxenburgerBasis(algo.getLattice(), minConfiance, minSupport);
		baseCouv.setJobObserver(taskObserver);
		taskObserver.setTitle(getDescription()+" Running Luxenburger Algorithm");
		baseCouv.run();

		new TableVisualization(new RulesBasis(rce.getSelectedRelation(), baseCouv.getBase(), minSupport, minConfiance), rce);
		
    	taskObserver.taskEnd();
		goodEnded=true;
		
		stringResult=baseCouv.getResultat();
  		
		rce.showTaskResult(this);

	}
	
	public void setMinSupport(double minSupport){
		this.minSupport=minSupport;
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
		return this.minSupport;
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
		LuxenburgerTask newTask=new LuxenburgerTask(rce);
		newTask.theBinRelOnUse=theBinRelOnUse;
		newTask.goodEnded=goodEnded;
		newTask.taskObserver=taskObserver;
		
		// Local values
		newTask.minSupport=this.minSupport;
		newTask.minConfiance = this.minConfiance;
		newTask.nomFichierEntre=this.nomFichierEntre;
		newTask.nomFichierSauvegardeApprox=this.nomFichierSauvegardeApprox;

		return newTask;
	}

}
