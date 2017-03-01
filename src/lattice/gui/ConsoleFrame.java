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
import java.awt.Graphics;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowListener;

import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JSplitPane;
import javax.swing.UIManager;

import lattice.command.RuleCommand;

/**
 * @author Mr ROUME
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public abstract class ConsoleFrame extends JFrame implements ActionListener, WindowListener {

	protected JMenuBar maBar;

	protected JMenu consoleMenu;
	protected JMenuItem showItem;
	protected JMenuItem hideItem;
	protected JMenuItem clearItem;

	protected JSplitPane splitPanel;
	protected JPanel topPanel;
	protected JPanel bottomPanel;
	private MainDesktop mainDesktop;
	protected Console console;
	protected boolean showConsole=true;
	
	private JLabel statutLabel = null;


	protected double DIVIDER_LOC = 0.7d;
	protected int FIX_LOC = -1;

	/**
	 * Constructor for ConsoleFrame.
	 * @throws HeadlessException
	 */
	public ConsoleFrame() {
		super();
		
		//setLookNFeel();

		initComponent();
	}
	
	/**
	 * Constructor for ConsoleFrame.
	 * @throws HeadlessException
	 */
	public ConsoleFrame(double div_loc) {
		super();
		DIVIDER_LOC=div_loc;

		//setLookNFeel();
		
		initComponent();
	}

	public Console getConsole() {
		return console;
	}

	public void initComponent() {
				// Initialisation Menu File
		initConsoleMenu();

		// Initialisation la Status Bar
		initStatusBar();

		// Initialisation de la fenetre interne
		initView();		

		
	}
		
		/**
	 * Sélectionne le lookand feel de l'OS
	 *
	 */
	private void setLookNFeel() {
		try {
			UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

/**
	  * Initialise le menu Console
	  *
	  */
	private void initConsoleMenu() {
		consoleMenu=new JMenu("Console");
		consoleMenu.setMnemonic('C');

		showItem=new JMenuItem("Show Console");
		showItem.setMnemonic('S');
		showItem.setAccelerator(
			javax.swing.KeyStroke.getKeyStroke(
				java.awt.event.KeyEvent.VK_S,
				java.awt.event.KeyEvent.CTRL_MASK,
				false));
		showItem.addActionListener(this);

		hideItem=new JMenuItem("Hide Console");
		hideItem.setAccelerator(
			javax.swing.KeyStroke.getKeyStroke(
				java.awt.event.KeyEvent.VK_H,
				java.awt.event.KeyEvent.CTRL_MASK,
				false));
		hideItem.setMnemonic('H');
		hideItem.addActionListener(this);

		clearItem=new JMenuItem("Clear Console");
		clearItem.setMnemonic('C');
		clearItem.setAccelerator(
			javax.swing.KeyStroke.getKeyStroke(
				java.awt.event.KeyEvent.VK_C,
				java.awt.event.KeyEvent.CTRL_MASK,
				false));
		clearItem.addActionListener(this);
		
		consoleMenu.add(showItem);
		consoleMenu.add(hideItem);
		consoleMenu.add(clearItem);

	}

	/**
	 * Initialise la barre d'état
	 *
	 */
	private void initStatusBar() {
/*		Dimension statusBarSize =
			new Dimension((int) this.getSize().getWidth(), 21);
		statutLabel=new JLabel("Galicia... Stated");
		statutLabel.setPreferredSize(statusBarSize);
		statutLabel.setBorder(BorderFactory.createLoweredBevelBorder());
		this.getContentPane().add(statutLabel, BorderLayout.SOUTH);*/
	}

	/**
	 * Initialise la vue de la fenetre interne
	 *
	 */
	private void initView() {
		console=new Console(new RuleCommand());
		mainDesktop=new MainDesktop();
		topPanel=new JPanel(new BorderLayout());
		topPanel.add(mainDesktop);
		bottomPanel=new JPanel(new BorderLayout());
		//bottomPanel.add(new JScrollPane(console), BorderLayout.CENTER);
		bottomPanel.add(console, BorderLayout.CENTER);
		splitPanel = new JSplitPane(JSplitPane.VERTICAL_SPLIT, topPanel, bottomPanel);
		getContentPane().add(splitPanel, BorderLayout.CENTER);		

	}
	
	public void actionPerformed(ActionEvent ae) {
		
		if(ae.getSource()==showItem) {
			//console.addMessage("Show Console...\n");
			showConsole=true;
			repaint();
		}
		
		if(ae.getSource()==hideItem) {
			//console.addMessage("Hide Console...\n");
			showConsole=false;
			repaint();
		}

		if(ae.getSource()==clearItem) {
			console.clear();
		}
		
	}
	
	public void setTopPanel(JComponent cmp) {
		topPanel.removeAll();
		topPanel.add(cmp, BorderLayout.CENTER);
	}

	public void setBottomPanel(JComponent cmp) {
		bottomPanel.removeAll();
		bottomPanel.add(cmp, BorderLayout.CENTER);
	}

	public void paint(Graphics g) {
		super.paint(g);
		if(showConsole) {
			if(FIX_LOC != -1) splitPanel.setDividerLocation(FIX_LOC);
			else splitPanel.setDividerLocation(DIVIDER_LOC);
		}
		else splitPanel.setDividerLocation(1d);
	}

/*
	public void paint(Graphics g) {
		super.paint(g);
		if(! showConsole) splitPanel.setDividerLocation(1d);
	}
*/
	public void addMessage(String newMess) {
		console.addMessage(newMess);
	}
}
