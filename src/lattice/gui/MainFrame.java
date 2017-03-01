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

package lattice.gui;

import java.awt.BorderLayout;
import java.awt.HeadlessException;
import java.awt.event.ActionEvent;
import java.awt.event.WindowEvent;
import java.util.Vector;

import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JToolBar;

import lattice.gui.tooltask.JobObservable;
import lattice.gui.tooltask.WaitingFrame;
import lattice.gui.util.ResourceManager;
import lattice.io.AbstractReader;
import lattice.io.AbstractWriter;
import lattice.io.ConsoleWriter;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.structure.CompleteConceptLattice;

/**
 * @author Mr ROUME
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class MainFrame
	extends OpenFileFrame {

	/* Composantes graphiques contenues dans ce cadre :
	 * Bare de Menu
	 * Menu File et ses Item (Editer, Ouvrire, Sauver, Quitter)
	 * Menu Help et ses Item (About)
	 * Une Bar d'outils et ses Items (Idem Menu File)
	 * Sattus Bar
	*/

	private JMenu fileMenu = null;
	private JMenuItem editItem = null;
	private JMenuItem openItem = null;
	private JMenuItem quitItem = null;

	private JMenu helpMenu = null;
	private JMenuItem aboutItem = null;

	private JToolBar jToolBar = null;
	private JButton openButton = null;
	private JButton saveButton = null;
	private JButton helpButton = null;
	private JButton closeButton = null;

	private Vector setOfRelationalContextEditor = null;

	/**
	 * Constructor for MainFrame.
	 * @throws HeadlessException
	 */
	public MainFrame() {
		super();
		setOfRelationalContextEditor = new Vector();

		// Initialisation de la Fenetre principale
		this.setTitle("Galicia v.2.0, Release Distribution - August 2004");
		addWindowListener(this);
		setFrameSize();
		initComponents();
		//addMessage("> Hello folks!");
		addMessage("> Welcome to Galicia\n");
	}

	/**
	 * Centrer la fenêtre
	 *
	 */
	private void setFrameSize() {

		setSize(640, 400);
		setLocation(100, 50);
	}

	/**
	 * Initialise et affiche cette vue a l ecran
	 *
	 */
	public void initComponents() {

		// Initialisation et Ajout de la Bare de Menu
		initMenuBar();

		// Initialisation de la Tool de menu
		initToolBar();

	}

	/**
	 * Initialise et Ajoute les éléments du menu
	 *
	 */
	private void initMenuBar() {
		// Initialisation Menu File
		initFileMenu();

		// Initialisation Menu Help
		initHelpMenu();

		maBar = new JMenuBar();
		maBar.add(fileMenu);
		maBar.add(consoleMenu);
		maBar.add(helpMenu);
		setJMenuBar(maBar);
		validate();
	}

	/**
	   * Initialise le menu File
	   *
	   */
	private void initFileMenu() {

		// Initialisation du menu
		fileMenu = new JMenu("File");
		fileMenu.setMnemonic('F');

		// Initialisation des items du menu
		editItem = new JMenuItem("New Context or Family of Contexts");
		editItem.setAccelerator(
			javax.swing.KeyStroke.getKeyStroke(
				java.awt.event.KeyEvent.VK_N,
				java.awt.event.KeyEvent.CTRL_MASK,
				false));
		editItem.setMnemonic('N');
		editItem.addActionListener(this);

		openItem = new JMenuItem("Open");
		openItem.setAccelerator(
			javax.swing.KeyStroke.getKeyStroke(
				79,
				java.awt.event.KeyEvent.CTRL_MASK,
				false));
		openItem.setMnemonic('O');
		openItem.addActionListener(this);

		quitItem = new JMenuItem("Quit");
		quitItem.setAccelerator(
			javax.swing.KeyStroke.getKeyStroke(
				81,
				java.awt.event.KeyEvent.CTRL_MASK,
				false));
		quitItem.setMnemonic('Q');
		quitItem.addActionListener(this);

		// Ajout des items au menu
		fileMenu.add(editItem);
		fileMenu.addSeparator();
		fileMenu.add(openItem);
		fileMenu.addSeparator();
		fileMenu.add(quitItem);

	}

	/**
	  * Initialise le menu Help
	  *
	  */
	private void initHelpMenu() {
		helpMenu = new JMenu("Help");
		helpMenu.setMnemonic('H');

		aboutItem = new JMenuItem("About");
		aboutItem.setMnemonic('A');
		aboutItem.addActionListener(this);


		helpMenu.add(aboutItem);

	}

	/**
	 * Initialise et Ajoute la ToolBar
	 *
	 */
	private void initToolBar() {
		
		openButton = new JButton(new ImageIcon(ResourceManager.getOpenImgURL()));
		openButton.setToolTipText("Open");
		openButton.addActionListener(this);

		saveButton = new JButton(new ImageIcon(ResourceManager.getSaveImgURL()));
		saveButton.setToolTipText("Save");
		saveButton.setEnabled(false);
		saveButton.addActionListener(this);

		closeButton = new JButton(new ImageIcon(ResourceManager.getCloseImgURL()));
		closeButton.setToolTipText("Close");
		closeButton.addActionListener(this);

		helpButton = new JButton(new ImageIcon(ResourceManager.getHelpImgURL()));
		helpButton.setToolTipText("About");
		helpButton.addActionListener(this);

		jToolBar = new JToolBar();
		jToolBar.add(openButton, null);
		jToolBar.addSeparator();
		jToolBar.add(closeButton, null);
		jToolBar.addSeparator();
		jToolBar.add(saveButton, null);
		jToolBar.addSeparator();
		jToolBar.add(helpButton, null);

		this.getContentPane().add(jToolBar, BorderLayout.NORTH);
	}

	// Gestionnaire des Action sur Bouton
	public void actionPerformed(ActionEvent ae) {
		super.actionPerformed(ae);

		if (ae.getSource() == editItem) {
			//addMessage("Action Edition\n");
			RelationalContextFamily rc = new RelationalContextFamily();
			RelationalContextEditor rce = new RelationalContextEditor(rc);
			rce.show();
			rce.addWindowListener(this);
			setOfRelationalContextEditor.add(rce);
		}

		if (ae.getSource() == openItem || ae.getSource() == openButton) {
			RelationalContextFamily rc = new RelationalContextFamily();
			RelationalContextEditor rce = new RelationalContextEditor(rc);
			rce.show();
			rce.addWindowListener(this);
			setOfRelationalContextEditor.add(rce);
			rce.openData();
		}

		if (ae.getSource() == quitItem || ae.getSource() == closeButton) {
			System.exit(0);
		}
		if (ae.getSource() == aboutItem || ae.getSource() == helpButton) {
			addMessage("About Galicia\n");
			String about=new String("Galicia Platform\n"+
			"Release: 2.0\n"+
			"Release Distribution"+
			"\n\n"+
			"(c) Copyrights University of Montreal (Canada), LIRMM (France), \n Université de la Réunion (France), UQAM (Canada), UQO (Canada)"+ 
			" 2002, 2004. \n All rights reserved.\n\n"+
			"The Galicia team acknowledges the contribution of all the designers "+
			"of the algorithms used by the platform:\n"+
			"CERES: Hervé Leblanc, Marianne Huchard (research supported by M. Dao, France Telecom R&D)\n"+
			"ARES:  Marianne Huchard, Hervé Dicky, Thérèse Libourel, Jean Villerd\n"+
			"ARES Dual: Jean Villerd (research supported by M. Dao, France Telecom R&D)\n"+
			"\n");
			JOptionPane.showMessageDialog(
			this,about,"About Galicia",JOptionPane.INFORMATION_MESSAGE);				
		}
				
	}

	// Gestionnaire des evennements sur Fenetres
	public void windowActivated(WindowEvent e) {
	}

	public void windowClosed(WindowEvent e) {
		if (e.getSource() == this)
			System.exit(0);
		if(e.getSource() instanceof WaitingFrame){
			if (((WaitingFrame)e.getSource()).getJob() instanceof AbstractReader && !((WaitingFrame)e.getSource()).goodWork()) {
				addMessage("Reading didn't work properly!\n");
			}
			if(((WaitingFrame)e.getSource()).getJob() instanceof AbstractWriter && ((WaitingFrame)e.getSource()).goodWork()){
				addMessage("Writing done!\n");
			}
			if (((WaitingFrame)e.getSource()).getJob() instanceof AbstractWriter && !((WaitingFrame)e.getSource()).goodWork()) {
				addMessage("Writing didn't work properly \n");
			}
			if(((WaitingFrame)e.getSource()).getJob() instanceof ConsoleWriter && ((WaitingFrame)e.getSource()).goodWork()){
				addMessage("Writing done!\n");
			}
			if (((WaitingFrame)e.getSource()).getJob()  instanceof ConsoleWriter && !((WaitingFrame)e.getSource()).goodWork()) {
				addMessage("Writing didn't work properly!\n");
			}
			JobObservable job = ((WaitingFrame)e.getSource()).getJob();
			if(job instanceof AbstractReader && ((AbstractReader)job).getData()!=null){
				RelationalContextFamily rc=null;
				if(((AbstractReader)job).getData() instanceof MatrixBinaryRelationBuilder) {
					rc=new RelationalContextFamily();
					rc.setName(((AbstractReader)job).getDefaultNameForData());
					MatrixBinaryRelationBuilder binRel=(MatrixBinaryRelationBuilder)((AbstractReader)job).getData();
					if(binRel.getName().equals(RelationBuilder.DEFAULT_NAME)) binRel.setName(((AbstractReader)job).getDefaultNameForData());
					rc.add(binRel);
				} 
				if(((AbstractReader)job).getData() instanceof RelationalContextFamily) {
					rc=(RelationalContextFamily)((AbstractReader)job).getData();
					if(rc.getName().equals(RelationalContextFamily.DEFAULT_NAME)) rc.setName(((AbstractReader)job).getDefaultNameForData());
				} 
				if(((AbstractReader)job).getData() instanceof CompleteConceptLattice) {
					CompleteConceptLattice cl=(CompleteConceptLattice)((AbstractReader)job).getData();
					rc=new RelationalContextFamily();
					rc.setName(((AbstractReader)job).getDefaultNameForData());
					MatrixBinaryRelationBuilder binRel=MatrixBinaryRelationBuilder.getInstanceFromLattice(cl);					
					if(binRel.getName().equals(RelationBuilder.DEFAULT_NAME)) binRel.setName(((AbstractReader)job).getDefaultNameForData());
					binRel.setLattice(cl);
					rc.add(binRel);					
				} 
				RelationalContextEditor rce = new RelationalContextEditor(rc);
				rce.addWindowListener(this);
				rce.show();
				if(((AbstractReader)job).getData() instanceof CompleteConceptLattice) rce.showAssociatedGraph();				
				setOfRelationalContextEditor.add(rce);
				addMessage("Opening done...\n");
			}
		}
		else {
			System.out.println("closed required!");
		}
	}

	public void windowClosing(WindowEvent e) {
		if (e.getSource() == this)
			System.exit(0);
		else {
			System.out.println("closing done");
			((JFrame) e.getSource()).dispose();
		}
	}
	public void windowDeactivated(WindowEvent e) {
	}
	public void windowDeiconified(WindowEvent e) {
	}
	public void windowIconified(WindowEvent e) {
	}
	public void windowOpened(WindowEvent e) {
	}	
}