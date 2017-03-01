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
 * Created on 3-May-2004
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package lattice.gui;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JMenu;
import javax.swing.JMenuItem;

import lattice.gui.controller.*;

/**
 * @author rouanehm
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class RCAView implements ActionListener {
	
	RCAController rcaCtrl;
	// Algorithms menu
	private JMenu menuRCA = null;	
	private JMenuItem multiFCAGeneral = null;
	private JMenuItem multiFCAUML = null;
	
	public RCAView(RCAController ctrl){
		rcaCtrl=ctrl;
	}
	
	public JMenu getMainMenu(){
		return menuRCA;
	}	
	
	public void initMenu(){
		
		menuRCA = new JMenu("Multi-FCA");
		menuRCA.setMnemonic('M');

		multiFCAGeneral = new JMenuItem("Interactive Multi-FCA");
		multiFCAGeneral.setMnemonic('I');
		multiFCAGeneral.addActionListener(this);
		menuRCA.add(multiFCAGeneral);
				
		multiFCAUML = new JMenuItem("Batch Multi-FCA on RCF-mapped UML model");
		multiFCAUML.setMnemonic('B');
		multiFCAUML.addActionListener(this);
		menuRCA.add(multiFCAUML);		
	}
	
	public void actionPerformed(ActionEvent arg0) {
		RelationalContextEditor rce = rcaCtrl.getRelationalContextEditor();
		if(arg0.getSource()==multiFCAGeneral){
	 		rcaCtrl.MultiFCAGeneral();
		}
		if(arg0.getSource()==multiFCAUML){
			rcaCtrl.MultiFCAUML();	 
		}
		rce.checkPossibleActions();
	}
	public void checkPossibleActions(){
			menuRCA.setEnabled(true);
			return;
	}
}
