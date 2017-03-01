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

package lattice.graph.trees.event;

/**
	* Adapter spécifique utilisé par EditeurDescriptif pour gérer les évenements
	* de mise en forme des arbres
*/

// import java;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import lattice.graph.trees.TreeEditor;

public class MenuAffichageAdapter implements ActionListener {

// Pour afficher la fen?tre de zoom
	public static final int AFF_ZOOM = 1;
	public static final int AFF_INFO = 21;
	public static final int FORMAT_1 = 2;
	public static final int FORMAT_2 = 3;
	public static final int FORMAT_3 = 4;
	public static final int FORMAT_4 = 5;
// Pour zoom
	public static final int ZOOM_MOINS = 6;
	public static final int ZOOM_PLUS = 7;
// Pour changer la forme des relations
	public static final int CHANGE_FORMEREL = 8;
	public static final int CHANGE_FLECHES = 9;
	public static final int POS_LIENS = 10;
	public static final int AFF_ATTRIB = 11;
	public static final int TEXT_RELATIONS = 12;

// Pour changer la fontes des objets et des attributs
	public static final int CHANGE_POLICE_OBJ = 13;
	public static final int CHANGE_POLICE_ATT = 14;
	public static final int CHANGE_POLICE_REL = 15;
	public static final int CHANGE_STYLE_OBJ  = 16;
	public static final int CHANGE_STYLE_ATT  = 17;
	public static final int CHANGE_STYLE_REL  = 18;

	public static final int SET_IMAGE = 19;
	public static final int SET_ALIGNEMENT = 20;
//  public static final int
	int choix;
	TreeEditor editeur;

	public MenuAffichageAdapter(int choix, TreeEditor editeur) {
		this.choix = choix;
		this.editeur = editeur;
	}

	public void actionPerformed(ActionEvent e) {
		//System.out.println("***"+e.getActionCommand()+"***");
		switch(choix) {
			case CHANGE_POLICE_OBJ: editeur.getCanvas().setPoliceObj(e.getActionCommand()); break;
			case CHANGE_POLICE_ATT: editeur.getCanvas().setPoliceAtt(e.getActionCommand()); break;
			case CHANGE_POLICE_REL: editeur.getCanvas().setPoliceRel(e.getActionCommand()); break;
			case CHANGE_STYLE_OBJ: editeur.getCanvas().setStyleObj(style(e.getActionCommand())); break;
			case CHANGE_STYLE_ATT: editeur.getCanvas().setStyleAtt(style(e.getActionCommand())); break;
			case CHANGE_STYLE_REL: editeur.getCanvas().setStyleRel(style(e.getActionCommand())); break;
			case AFF_ZOOM: editeur.changeAffZoomViewer2();					break;
			case FORMAT_1: editeur.getCanvas().setFormatter(1);				break;
			case FORMAT_2: editeur.getCanvas().setFormatter(3);				break;
			case FORMAT_3: editeur.getCanvas().setFormatter(5);				break;
			case FORMAT_4: editeur.getCanvas().setFormatter(4);				break;
			case ZOOM_MOINS: editeur.getCanvas().ZM();						break;
			case ZOOM_PLUS: editeur.getCanvas().ZP();						break;
			case CHANGE_FORMEREL: editeur.changeFormeRelation();			break;
			case CHANGE_FLECHES: editeur.changeFleches();					break;
			case POS_LIENS: editeur.posLiens();								break;
			case AFF_ATTRIB: editeur.affAttributs2();						break;
			case TEXT_RELATIONS: editeur.changeTextRelation();				break;
			case SET_IMAGE :  editeur.loadBackgroundPicture();				break;
			case SET_ALIGNEMENT : editeur.getCanvas().setBgAlignment(e.getActionCommand()); break ;
			case AFF_INFO : editeur.changeAffInfo();								break;
			default: 											 			break;
		}// fin switch
	}

	public int style(String s) {
		if(s.equals("Italique")) return Font.ITALIC;
		if(s.equals("Gras")) return Font.BOLD;
		if(s.equals("Gras italique")) return (Font.ITALIC+Font.BOLD);
		else return Font.PLAIN;

	}
}