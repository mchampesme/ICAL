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

// package ikbs.graphics.eventpackage lattice.graph.trees.event;import java.awt.event.ActionEvent;import java.awt.event.ActionListener;import lattice.graph.trees.Editor;public class EditorAdapter implements ActionListener {	public static final int NULL = 0;	public static final int A_PROPOS = 1;	public static final int MANUEL = 2;	Editor editeur;	int choix;	public EditorAdapter(int choix, Editor editeur) {		this.choix = choix;		this.editeur = editeur;	}	public void actionPerformed(ActionEvent e) {		switch(choix) {			case A_PROPOS: editeur.afficherAPropos(); break;			case MANUEL: editeur.afficherAide(); break;			default: break;		}// fin switch	}}