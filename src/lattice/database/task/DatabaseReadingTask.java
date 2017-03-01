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

import lattice.database.io.DatabaseAbstractReader;
import lattice.gui.RelationalContextEditor;
import lattice.gui.tooltask.AbstractTask;
import lattice.gui.tooltask.WaitingStepTaskFrame;

/**
 * A class to create a database reading task 
 * @author Manuel Aupetit
 */
public class DatabaseReadingTask extends AbstractTask {

	private RelationalContextEditor relCtxEd = null;
	private DatabaseAbstractReader reader = null;
	private Object dataResult = null;
	private String defaultNameForData = "Default Name";
	
	public DatabaseReadingTask(RelationalContextEditor relCtxEd){
		this.relCtxEd = relCtxEd;
	}

	/* (non-Javadoc)
	 * @see lattice.gui.tooltask.StepTaskObservable#exec()
	 */
	public void exec() {
		goodEnded = false;
		DatabaseReadingTask newTask = (DatabaseReadingTask)clone();
		newTask.taskObserver = new WaitingStepTaskFrame(newTask,1,relCtxEd.getConsole());
	}

	/* (non-Javadoc)
	 * @see lattice.gui.tooltask.JobObservable#getDescription()
	 */
	public String getDescription() {
		return "Database Reading Task:";
	}

	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		reader.setJobObserver(taskObserver);
		taskObserver.setTitle(getDescription() + " Processing...");
		reader.run();
		taskObserver.jobEnd(true);
		taskObserver.taskEnd();
		goodEnded = true;
		dataResult = reader.getData();
		relCtxEd.showTaskResult(this);
	}
	
	public Object getData(){
		return dataResult;
	}
	
	public String getDefaultNameForData(){
		return defaultNameForData;
	}

	public void setDataReader(DatabaseAbstractReader reader){
		this.reader = reader;
		this.defaultNameForData = reader.getDefaultNameForData();
	}
	
	public Object clone(){
		DatabaseReadingTask readTask = new DatabaseReadingTask(relCtxEd);
		readTask.setDataReader(reader);
		readTask.goodEnded = goodEnded;
		return readTask;
	}
	
}
