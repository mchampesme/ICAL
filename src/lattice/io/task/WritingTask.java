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
 * Created on 13 juil. 2003
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package lattice.io.task;

import lattice.gui.RelationalContextEditor;
import lattice.gui.tooltask.AbstractTask;
import lattice.gui.tooltask.WaitingStepTaskFrame;
import lattice.io.AbstractWriter;
import lattice.io.ConsoleWriter;
import lattice.util.relation.RelationalContextFamily;

/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class WritingTask extends AbstractTask {

	private RelationalContextEditor rce=null;
	private AbstractWriter aw=null;
	private Object data=null;

	public WritingTask(RelationalContextEditor rce){
		this.rce=rce;
	}

	/* (non-Javadoc)
	 * @see lattice.gui.tooltask.StepTaskObservable#exec()
	 */
	public void exec() {
		goodEnded=false;
		WritingTask newTask=(WritingTask)clone();
		if(newTask.getData() instanceof RelationalContextFamily){
			newTask.taskObserver = new WaitingStepTaskFrame(newTask,1,rce.getConsole());
			//newTask.taskObserver = new WaitingSetpTaskFrame(newTask,((RelationalContext)newTask.getData()).getNumberOfRelation(),rce.getConsole());
		} else newTask.taskObserver = new WaitingStepTaskFrame(newTask,1,rce.getConsole());		
	}

	/* (non-Javadoc)
	 * @see lattice.gui.tooltask.JobObservable#getDescription()
	 */
	public String getDescription() {
		return "Writing Task :";
	}

	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		aw.setJobObserver(taskObserver);
		taskObserver.setTitle(getDescription()+" Processing...");
		aw.run();
		taskObserver.jobEnd(true);
		taskObserver.taskEnd();
		goodEnded=true;
		rce.showTaskResult("Writing done!\n");
	}
	
	public void setDataWriter(AbstractWriter aw){
		this.aw=aw;
		this.data=aw.getData();
	}
	public void setConsoleWriter(ConsoleWriter aw){
		this.aw=aw;
		this.data=aw.getData();
	}
	
	public void setData(Object data){
		this.data=data;
	}
	public Object getData(){
		return data;
	}
	
	public Object clone(){
		WritingTask wt=new WritingTask(rce);
		wt.setDataWriter(aw);
		wt.setData(data);
		wt.goodEnded=goodEnded;
		return wt;
	}


}
