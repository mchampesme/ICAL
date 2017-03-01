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

package lattice.graph.utils;

// import java;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import lattice.graph.trees.GraphViewer;

public class ArbreAdapter implements ActionListener {
	public static final int FRANCAIS = 0;
	public static final int ANGLAIS = 1;

	public static final int SAVE = 2;
	public static final int LOAD = 3;
	public static final int LOAD_DIST = 4;
	public static final int FORME_SIMPLE = 5;
	public static final int FORME_EQUI = 6;
	public static final int GRAPHE = 7;
	public static final int FORME_VERT = 8;
	public static final int ZOOM_PLUS = 9;
	public static final int ZOOM_MOINS = 10;
	public static final int ZOOM = 11;
	public static final int AFF_ATT = 12;
	public static final int EDITION = 13;
	public static final int AFFICHER_WEB = 14;

	//TreeEditor editeur;
	EditeurArbreInterface editeur;
	int choix;

	public ArbreAdapter(int choix, EditeurArbreInterface editeur) {
		this.choix = choix;
		this.editeur = editeur;

	}

	public void actionPerformed(ActionEvent e) {
		int choix = this.choix;

		// Si la source de l'évenement implémente l'interface ChoixComponent
		// et par conséquent qu'elle implémente la fonction getChoix, alors on
		// récup?re l'entier associé à l'action directement par l'instance
		if(e.getSource() instanceof ChoixComponent) {
			choix = ((ChoixComponent) e.getSource()).getChoix();
		}
		switch(choix) {
			case SAVE: editeur.sauverLocal(); break;
			case LOAD: editeur.loadLocal(); break;
			case LOAD_DIST: editeur.loadDistant(); break;
			case FORME_SIMPLE: editeur.getCanvas().setFormatter(GraphViewer.FORMATTER_GD2) ; break;
			case FORME_EQUI: editeur.getCanvas().setFormatter(GraphViewer.FORMATTER_GD4) ; break;
			case GRAPHE: editeur.getCanvas().setFormatter(GraphViewer.FORMATTER_GD5) ; break;
			case FORME_VERT: editeur.getCanvas().setFormatter(GraphViewer.FORMATTER_HB) ; break;
			case ZOOM_PLUS: editeur.getCanvas().ZP(); break;
			case ZOOM_MOINS: editeur.getCanvas().ZM(); break;
			case ZOOM: editeur.changeAffZoomViewer() ; break;
			case AFF_ATT: editeur.affAttributs(); break;
			case EDITION: editeur.changeMode(); break;
			case AFFICHER_WEB: editeur.showDocument(); break;
			case FRANCAIS: editeur.changeLangue(FRANCAIS); break;
			case ANGLAIS: editeur.changeLangue(ANGLAIS); break;
			default: break;
		}

	}
}