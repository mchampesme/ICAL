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

package lattice.graph.trees;/**	* IKBS - PopUpMenu du canvas	* Version 1.0	* David Grosser - 9 Juillet 1998	* Modifié le  9 Juillet 1998*/// import javaimport java.awt.MenuItem;import java.awt.PopupMenu;import lattice.graph.trees.event.IkbsPopupMenuListener;public class IkbsPopupMenu extends PopupMenu {	public IkbsPopupMenu(String titre, ActionGraphViewer unCanvas) {		super(titre);		MenuItem mi;		mi = new MenuItem("Créer objet");		mi.addActionListener(new IkbsPopupMenuListener(IkbsPopupMenuListener.CREER_OBJET, unCanvas));		add(mi);		addSeparator();		mi = new MenuItem("Tout effacer");		mi.addActionListener(new IkbsPopupMenuListener(IkbsPopupMenuListener.TOUT_EFFACER, unCanvas));		add(mi);		/**addSeparator();		mi = new MenuItem("Coller");		mi.addActionListener(new IkbsPopupMenuListener(IkbsPopupMenuListener.COLLER, unCanvas));		add(mi);*/	}}// fin classe IkbsPopupMenu