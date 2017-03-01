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
package lattice.algorithm.task;

import lattice.algorithm.LatticeAlgorithm;
import lattice.gui.RelationalContextEditor;
import lattice.gui.tooltask.AbstractTask;
import lattice.gui.tooltask.WaitingStepTaskFrame;

/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class LatticeAlgorithmTask extends AbstractTask {

	LatticeAlgorithm algo=null;
	private RelationalContextEditor rce=null;

	public LatticeAlgorithmTask(RelationalContextEditor rce){
		this.rce=rce;
	}
		
	public void setAlgo(LatticeAlgorithm algo){
		this.algo=algo;
	}

	public LatticeAlgorithm getAlgo(){
		 return algo;
	}

	/* (non-Javadoc)
	 * @see lattice.gui.tooltask.StepTaskObservable#exec()
	 */
	public void exec() {
		goodEnded=false;
		LatticeAlgorithmTask newTask=(LatticeAlgorithmTask)clone();
		newTask.taskObserver = new WaitingStepTaskFrame(newTask,1,rce.getConsole());
	}

	/* (non-Javadoc)
	 * @see lattice.gui.tooltask.JobObservable#getDescription()
	 */
	public String getDescription() {
		return "Algorithm Execution: ";
	}

	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		algo.setJobObserver(taskObserver);
		taskObserver.setTitle(getDescription()+" Processing "+algo.getDescription());
		//LatticeNode.resetNodeId();
		algo.run();
		taskObserver.jobEnd(true);
		taskObserver.taskEnd();
		goodEnded=true;
		rce.showTaskResult(this);
	}

	public Object clone(){
		LatticeAlgorithmTask newTask=new LatticeAlgorithmTask(rce);
		newTask.algo=algo;
		newTask.theBinRelOnUse=theBinRelOnUse;
		newTask.goodEnded=goodEnded;
		newTask.taskObserver=taskObserver;
		return newTask;
	}
}
