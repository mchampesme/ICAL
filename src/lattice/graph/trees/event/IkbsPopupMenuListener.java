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

package lattice.graph.trees.event;/**	* IKBS - IkbsPopupMenuListener implements ActionListener	* Version 1.0	* David Grosser - 9 Juillet 1998	* Modifié le  9 Juillet 1998*/// import javaimport java.awt.event.ActionEvent;import java.awt.event.ActionListener;import lattice.graph.trees.ActionGraphViewer;/**	* IKBS trees.event	* Implémente les actions associées au popUp des objets et des attributs*/public class IkbsPopupMenuListener implements ActionListener {// Constantes	public static final int CREER_OBJET 		= 0;	public static final int EFFACER_OBJET 		= 1;	public static final int EFFACER_SOUS_ARBRE  = 2;	public static final int EDITER_OBJET		= 3;	public static final int RACINE_OBJET		= 4;	public static final int CREER_ATTRIBUT		= 5;	public static final int COLLER 	 			= 6;	public static final int COPIER_OBJET		= 7;	public static final int COPIER_SOUS_ARBRE	= 8;	public static final int TOUT_EFFACER		= 9;	public static final int EDITER_ATTRIBUT 	= 10;	public static final int CIBLE_ATTRIBUT		= 11;	public static final int EFFACER_ATTRIBUT	= 12;	public static final int COPIER_ATTRIBUT		= 13;	public static final int AFFICHER_ATT		= 14;	public static final int AFFICHER_FILS		= 15;// Variables d'instance	protected ActionGraphViewer graphEditor;	protected int choix;	public IkbsPopupMenuListener(int choix, ActionGraphViewer unCanvas) {		this.graphEditor = unCanvas;		this.choix = choix;	}	public void actionPerformed(ActionEvent e) {		switch(choix) {			case CREER_OBJET:				graphEditor.createNode();				break;			case EFFACER_OBJET:				graphEditor.eraseNode();				break;			case EFFACER_SOUS_ARBRE:				graphEditor.eraseTree();				break;			case EDITER_OBJET:				graphEditor.editNode();				break;			case RACINE_OBJET:				graphEditor.rootOnNode();				break;			case TOUT_EFFACER:				graphEditor.eraseAll();				break;			case COPIER_OBJET:				graphEditor.copyNode();				break;			case COPIER_SOUS_ARBRE:				graphEditor.copyTree();				break;			case CIBLE_ATTRIBUT:				graphEditor.setAttributCible();				break;			case EDITER_ATTRIBUT:				graphEditor.editerAttribut();				break;			case EFFACER_ATTRIBUT:				graphEditor.eraseAttribut();				break;			case COPIER_ATTRIBUT:				graphEditor.copyAttribut();				break;			case AFFICHER_ATT:				graphEditor.changeAffAttributs();				break; //on affiche la liste des attributs			case AFFICHER_FILS:				graphEditor.affSousArbre();				break;			default:				break;		}//fin switch	}}