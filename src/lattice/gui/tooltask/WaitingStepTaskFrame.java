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

import java.awt.BorderLayout;
import java.awt.event.WindowEvent;

import javax.swing.JPanel;
import javax.swing.JProgressBar;

import lattice.gui.ConsoleFrame;
import lattice.gui.MessageWriter;

/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class WaitingStepTaskFrame
	extends ConsoleFrame
	implements StepTaskObserver {

		private boolean goodJob = false;
		private StepTaskObservable work;
		private JProgressBar progressBarTask;
		private JProgressBar progressBarJob;
		private Thread theThread;
		private MessageWriter outputMessage;
		private int maxStep=1;
		private int currentStep=0;

	/**
	 * 
	 */
	public WaitingStepTaskFrame() {
		super();
		// TODO Auto-generated constructor stub
	}

	/**
	 * Constructor for WaitingSetpTaskFrame.
	 */
	public WaitingStepTaskFrame(StepTaskObservable theWork,int maxStep,MessageWriter outputMessage) {
		super(0.9d);
		setSize(600,300);
		setLocation(200,200);
		setTitle(theWork.getDescription());
		addWindowListener(this);

		bottomPanel.removeAll();
		JPanel panelSud=new JPanel(new BorderLayout());
		progressBarTask=new JProgressBar(0,100);
		progressBarJob=new JProgressBar(0,100);
		if(maxStep==1){
			panelSud.add(progressBarJob,BorderLayout.CENTER);
		}else{
			panelSud.add(progressBarTask,BorderLayout.NORTH);
			panelSud.add(progressBarJob,BorderLayout.SOUTH);
		}
		setBottomPanel(panelSud);
		
		work=theWork; 
		work.setJobObserver(this);
 
		this.outputMessage=outputMessage;
		this.maxStep=maxStep;

		show();
	}

	/* (non-Javadoc)
	 * @see lattice.util.tooltask.JobObserver#setPercentageOfWork(int)
	 */
	public void setPercentageOfWork(int i) {
		progressBarJob.setValue(i);
		//setPercentageOfStep(((currentStep*100)+progressBarJob.getValue())/maxStep);
	}

	/* (non-Javadoc)
	 * @see lattice.util.tooltask.JobObserver#setPercentageOfWork(int)
	 */
	public void setPercentageOfStep(int i) {
		progressBarTask.setValue(i);		
	}

	public void setMaxStep(int maxStep){
		this.maxStep=maxStep;
	}

	/* (non-Javadoc)
	 * @see lattice.util.tooltask.JobObserver#sendMessage(java.lang.String)
	 */
	public void sendMessage(String aMess) {
		outputMessage.addMessage(aMess);
	}

	/* (non-Javadoc)
	 * @see lattice.util.tooltask.JobObserver#jobEnd(boolean)
	 */
	public void jobEnd(boolean isGood) {
		this.goodJob=isGood;
		currentStep++;
		setPercentageOfStep((currentStep*100)/maxStep);
	}

	/* (non-Javadoc)
	 * @see lattice.util.tooltask.JobObserver#jobEnd(boolean)
	 */
	public void taskEnd() {
		dispose();
	}

	/* (non-Javadoc)
	 * @see lattice.util.tooltask.JobObserver#setJobObservable(lattice.util.tooltask.JobObservable)
	 */
	public void setJobObservable(JobObservable jO) {
		// TODO Auto-generated method stub

	}

	
	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowOpened(java.awt.event.WindowEvent)
	 */
	public void windowOpened(WindowEvent arg0) {
		progressBarJob.setValue(0);
		progressBarTask.setValue(0);
		theThread = new Thread(work);
		theThread.start();
	}

	/* (non-Javadoc)
	 * @see java.awt.event.WindowListener#windowClosing(java.awt.event.WindowEvent)
	 */
	public void windowClosing(WindowEvent arg0) {
		work.sendMessage(getTitle() +"... CANCELLED!\n");
		theThread.stop();
		dispose();
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
