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

// package ikbs.graphics.action
package lattice.graph.trees.event;

// import java;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import lattice.graph.trees.TreeEditor;
import lattice.graph.trees.menu.MenuItemColor;

public class MenuColorAdapter implements ActionListener {
	public static final int TEXT_OBJET = 1;
	public static final int FOND_OBJET = 2;
	public static final int TEXT_ATT = 3;
	public static final int FOND_ATT = 4;

	int choix;
	TreeEditor editeur;

	public MenuColorAdapter(int choix, TreeEditor editeur) {
		this.choix = choix;
		this.editeur = editeur;
	}

	public void actionPerformed(ActionEvent e) {
		MenuItemColor mic = (MenuItemColor) e.getSource();
		switch(choix) {
			case TEXT_OBJET: editeur.getCanvas().changeLabelColor(mic.getColor()); 	break;
			case FOND_OBJET: editeur.getCanvas().changeBgColor(mic.getColor()); 		break;
			case TEXT_ATT: editeur.getCanvas().changeLabelColorAtt(mic.getColor()); 	break;
			case FOND_ATT: editeur.getCanvas().changeBgColorAtt(mic.getColor()); 		break;
			default: break;
		}
	}
}