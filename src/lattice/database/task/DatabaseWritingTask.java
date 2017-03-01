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
 * Created on 2004-06-22
 * @author Manuel Aupetit
 */
package lattice.database.task;

import lattice.database.io.DatabaseAbstractWriter;
import lattice.gui.RelationalContextEditor;
import lattice.gui.tooltask.AbstractTask;
import lattice.gui.tooltask.WaitingStepTaskFrame;

/**
 * A class to create a database reading task 
 * @author Manuel Aupetit
 */
public class DatabaseWritingTask extends AbstractTask {

	private RelationalContextEditor relCtxEd = null;
	private DatabaseAbstractWriter writer = null;
	private Object dataResult = null;
	private String defaultNameForData = "Default Name";
	
	public DatabaseWritingTask(RelationalContextEditor relCtxEd){
		this.relCtxEd = relCtxEd;
	}

	/* (non-Javadoc)
	 * @see lattice.gui.tooltask.StepTaskObservable#exec()
	 */
	public void exec() {
		goodEnded = false;
		DatabaseWritingTask newTask = (DatabaseWritingTask)clone();
		newTask.taskObserver = new WaitingStepTaskFrame(newTask, 1, relCtxEd.getConsole());
	}

	/* (non-Javadoc)
	 * @see lattice.gui.tooltask.JobObservable#getDescription()
	 */
	public String getDescription() {
		return "Database Writing Task:";
	}

	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		writer.setJobObserver(taskObserver);
		taskObserver.setTitle(getDescription() + " Processing...");
		writer.run();
		taskObserver.jobEnd(true);
		taskObserver.taskEnd();
		goodEnded = true;
		dataResult = writer.getData();
		relCtxEd.showTaskResult(this);
	}
	
	public Object getData(){
		return dataResult;
	}
	
	public String getDefaultNameForData(){
		return defaultNameForData;
	}

	public void setDataWriter(DatabaseAbstractWriter writer){
		this.writer = writer;
		this.defaultNameForData = writer.getDefaultNameForData();
	}
	
	public Object clone(){
		DatabaseWritingTask writeTask = new DatabaseWritingTask(relCtxEd);
		writeTask.setDataWriter(writer);
		writeTask.goodEnded = goodEnded;
		return writeTask;
	}
	
}
