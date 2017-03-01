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

package lattice.graph.trees;/**	* IKBS - PopUpMenu des objets	* Version 1.0	* David Grosser - 9 Juillet 1998	* Modifié le  9 Juillet 1998*/// import javaimport java.awt.MenuItem;import java.awt.PopupMenu;import lattice.graph.trees.event.IkbsPopupMenuListener;import lattice.graph.trees.menu.MenuItemChange;public class ComponentPopUp extends PopupMenu {	protected MenuItemChange menuAtt, menuFils;	//protected boolean isFils = true; // true si le composant a des fils, true sinon	public ComponentPopUp(String titre, ActionGraphViewer action) {		super(titre);		init(action);	}	public void init(ActionGraphViewer unCanvas) {		MenuItem mi = new MenuItem("Editer objet");		mi.addActionListener(new IkbsPopupMenuListener(IkbsPopupMenuListener.EDITER_OBJET, unCanvas));		add(mi);		addSeparator();		menuAtt = new MenuItemChange("Afficher attributs", "Masquer attributs");		menuAtt.addActionListener(new IkbsPopupMenuListener(IkbsPopupMenuListener.AFFICHER_ATT, unCanvas));		add(menuAtt);		menuFils = new MenuItemChange("Afficher fils", "Masquer fils");		menuFils.addActionListener(new IkbsPopupMenuListener(IkbsPopupMenuListener.AFFICHER_FILS, unCanvas));		add(menuFils);		addSeparator();		mi = new MenuItem("Effacer objet");		mi.addActionListener(new IkbsPopupMenuListener(IkbsPopupMenuListener.EFFACER_OBJET, unCanvas));		add(mi);		mi = new MenuItem("Effacer sous arbre");		mi.addActionListener(new IkbsPopupMenuListener(IkbsPopupMenuListener.EFFACER_SOUS_ARBRE, unCanvas));		add(mi);		addSeparator();		mi = new MenuItem("Dupliquer objet");		mi.addActionListener(new IkbsPopupMenuListener(IkbsPopupMenuListener.COPIER_OBJET, unCanvas));		add(mi);		mi = new MenuItem("Dupliquer sous arbre");		mi.addActionListener(new IkbsPopupMenuListener(IkbsPopupMenuListener.COPIER_SOUS_ARBRE, unCanvas));		add(mi);	}	public void setLabelAtt(boolean b) {		menuAtt.setState(b);	}	public void setLabelFils(boolean b) {		menuFils.setState(b);	}}// fin classe IkbsPopupMenu