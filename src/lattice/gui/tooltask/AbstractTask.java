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
package lattice.gui.tooltask;

import java.awt.event.WindowEvent;
import java.util.List;
import java.util.Vector;

import lattice.util.relation.MatrixBinaryRelationBuilder;

/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract class AbstractTask implements StepTaskObservable {

	protected WaitingStepTaskFrame taskObserver=null; // La fenetre avec des progress bar
	protected boolean goodEnded=false;
	protected List<MatrixBinaryRelationBuilder> theBinRelOnUse=new Vector<MatrixBinaryRelationBuilder>(); // Les relations utilisés par la tache courante et qui devrons être relachés a l'issue

	public void setBinRelOnUse(List<MatrixBinaryRelationBuilder> theBinRelOnUse){
		this.theBinRelOnUse=theBinRelOnUse;
	}
	public List<MatrixBinaryRelationBuilder> getBinRelOnUse(){
		return theBinRelOnUse;
	}

	public boolean isGoodEnded(){
		return goodEnded;
	}

	public void setJobObserver(JobObserver jO) {
		// Nothing to do in Task

	}

	/* (non-Javadoc)
	 * @see lattice.gui.tooltask.JobObservable#sendJobPercentage(int)
	 */
	public void sendJobPercentage(int i) {
		// Nothing to do in Task

	}

	/* (non-Javadoc)
	 * @see lattice.gui.tooltask.JobObservable#sendMessage(java.lang.String)
	 */
	public void sendMessage(String aMess) {
		if(taskObserver!=null) taskObserver.sendMessage(aMess);
	}


	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowOpened(java.awt.event.WindowEvent)
	 */
	public void windowOpened(WindowEvent arg0) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowClosing(java.awt.event.WindowEvent)
	 */
	public void windowClosing(WindowEvent arg0) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowClosed(java.awt.event.WindowEvent)
	 */
	public void windowClosed(WindowEvent arg0) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowIconified(java.awt.event.WindowEvent)
	 */
	public void windowIconified(WindowEvent arg0) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowDeiconified(java.awt.event.WindowEvent)
	 */
	public void windowDeiconified(WindowEvent arg0) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowActivated(java.awt.event.WindowEvent)
	 */
	public void windowActivated(WindowEvent arg0) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowDeactivated(java.awt.event.WindowEvent)
	 */
	public void windowDeactivated(WindowEvent arg0) {
		// TODO Auto-generated method stub

	}


}
