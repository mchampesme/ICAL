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
import lattice.algorithm.ValtchevEtAl2;
import lattice.gui.RelationalContextEditor;
import lattice.gui.tooltask.WaitingStepTaskFrame;
import rule.algorithm.ValtchevAlOnlineBasisUpdate;
import rule.gui.TableVisualization;
import rule.io.XmlRuleExport;
import rule.util.RulesBasis;
import lattice.util.relation.MatrixBinaryRelationBuilder;

/**
 * @author frambouc
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class VNATask extends ruleAbstractTask {


  private double minSupport = 0.0d;
  private double minConfiance = 0.5d;

  private String choix;
  private String nomFichierEntre;
  private String nomFichierSauvegardeExact;
  private String nomFichierSauvegardeApprox;

  /**
   *
   */
  public VNATask(RelationalContextEditor rce) {
    super();
    this.rce=rce;
  }

  /* (non-Javadoc)
   * @see lattice.util.tooltask.JobObservable#getDescription()
   */
  public String getDescription() {
    return "Valtchev & al. (2003)";
  }

  public void exec(){
    goodEnded=false;
    VNATask newTask=(VNATask)clone();
    newTask.taskObserver = new WaitingStepTaskFrame(newTask,1,rce.getConsole());
  }

  /* (non-Javadoc)
   * @see java.lang.Runnable#run()
   */
  public void run() {
  	
  	// --- step 1
  	LatticeAlgorithm algo = new ValtchevEtAl2( (MatrixBinaryRelationBuilder) rce.
  			getSelectedRelation());
  	rce.addMessage("Processing " + algo.getDescription() +
  			" on the binary relation \"" +
  			( (MatrixBinaryRelationBuilder) rce.getSelectedRelation()).
  			getName() + "\"");
  	algo.setJobObserver(taskObserver);
  	taskObserver.setTitle(getDescription() +
  	" Processing Valtchev & al. lattice Algo.");
  	algo.run();
  	taskObserver.jobEnd(true);

  	// --- step 2
  	ValtchevAlOnlineBasisUpdate VNA = new ValtchevAlOnlineBasisUpdate(algo.getLattice(), minConfiance, 
  			choix);
  	VNA.setJobObserver(taskObserver);
  	taskObserver.setTitle(getDescription() +
  	" Processing Valtchev & al. rules Algo.");
  	VNA.run();
  	taskObserver.jobEnd(true);
  	taskObserver.taskEnd();
  	//goodEnded = true;

  	// --- step 3
  	
  	XmlRuleExport sauvegarde = new XmlRuleExport();
  	
  	if (choix.equals("0")|| choix.equals("2")){
  		new TableVisualization(new RulesBasis(rce.getSelectedRelation(), VNA.getExactRuleBasis(), minSupport, minConfiance), rce);
  	}
  	if (choix.equals("1") || choix.equals("2")) {
  		new TableVisualization(new RulesBasis(rce.getSelectedRelation(), VNA.getApproxRuleBasis(), minSupport, minConfiance), rce);
  	}
  	taskObserver.jobEnd(true);
  	taskObserver.taskEnd();
  	goodEnded=true;
  	stringResult = VNA.getResultat();
  	rce.showTaskResult(this);
  }
  public void setMinSupport(double minSupport){
	this.minSupport=minSupport;
  }
  public void setMinConfiance(double minConfiance){
	this.minConfiance=minConfiance;
  }
  public void setChoix(String choix){
  	this.choix=choix;
  }
  public void setNomFichierEntre(String nomFichierEntre){
	this.nomFichierEntre=nomFichierEntre;
  }
  public void setNomFichierSauvegardeExact(String nomFichierSauvegardeExact){
	this.nomFichierSauvegardeExact=nomFichierSauvegardeExact;
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
  public String getChoix(){
	return this.choix;
  }
  public String getNomFichierEntre(){
	return this.nomFichierEntre;
  }
  public String getNomFichierSauvegardeExact(){
	return this.nomFichierSauvegardeExact;
  }
  public String getNomFichierSauvegardeApprox(){
	return this.nomFichierSauvegardeApprox;
  }

  public Object clone(){
    VNATask newTask=new VNATask(rce);
    newTask.theBinRelOnUse=theBinRelOnUse;
    newTask.goodEnded=goodEnded;
    newTask.taskObserver=taskObserver;

	// Local values
	newTask.minSupport=this.minSupport;
	newTask.minConfiance = this.minConfiance;
	newTask.choix=this.choix;
	newTask.nomFichierEntre=this.nomFichierEntre;
	newTask.nomFichierSauvegardeExact=this.nomFichierSauvegardeExact;
	newTask.nomFichierSauvegardeApprox=this.nomFichierSauvegardeApprox;

    return newTask;
  }
}