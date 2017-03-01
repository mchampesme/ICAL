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

package lattice.gui.tooltask;

import java.awt.event.WindowEvent;

import javax.swing.JProgressBar;

import lattice.gui.Console;
import lattice.gui.ConsoleFrame;
 
/**
 * @author Mr ROUME
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class WaitingFrame extends ConsoleFrame implements JobObserver {

	private boolean goodJob = false;
	private JobObservable work;
	private JProgressBar progressBar;
	private Thread theThread;

	/**
	 * Constructor for WaitingFrame.
	 */
	public WaitingFrame(JobObservable theWork,Console outputConsole) {
		super(0.9d);
		setSize(400,300);
		setLocation(200,200);
		setTitle(theWork.getDescription());
		
		bottomPanel.removeAll();
		progressBar=new JProgressBar(0,100);
		setBottomPanel(progressBar);
		
		work=theWork; 
		work.setJobObserver(this);
 
		console=outputConsole;
		show();
	}
	
	public void sendMessage(String aMess){
		console.addMessage(aMess);
	}
	
	public void setPercentageOfWork(int val){
		progressBar.setValue(val);
		validate();
	}

	public void jobEnd(boolean isGood) {
		goodJob=isGood;
		this.dispose();
	}
	
	public void setJobObservable(JobObservable jO) {
		work=jO;
	}
	public void Start() {
		progressBar.setValue(0);
		theThread = new Thread(work);
		theThread.start();
	}

	public JobObservable getJob(){
		return work;
	}
	
	public boolean goodWork(){
		return goodJob;
	}
	
	//----------------------------------------------------------------------------
	//----------------------------------------------------------------------------
	//----------------      window listener         ------------------------------
	
	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowActivated(java.awt.event.WindowEvent)
	 */
	public void windowActivated(WindowEvent arg0) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowClosed(java.awt.event.WindowEvent)
	 */
	public void windowClosed(WindowEvent arg0) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowClosing(java.awt.event.WindowEvent)
	 */
	public void windowClosing(WindowEvent arg0) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowDeactivated(java.awt.event.WindowEvent)
	 */
	public void windowDeactivated(WindowEvent arg0) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowDeiconified(java.awt.event.WindowEvent)
	 */
	public void windowDeiconified(WindowEvent arg0) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowIconified(java.awt.event.WindowEvent)
	 */
	public void windowIconified(WindowEvent arg0) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowOpened(java.awt.event.WindowEvent)
	 */
	public void windowOpened(WindowEvent arg0) {
		// TODO Auto-generated method stub

	}

}
