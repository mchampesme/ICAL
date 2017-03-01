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

package lattice.graph.trees.formatter;import java.awt.Point;import java.awt.Rectangle;import java.util.Vector;import lattice.graph.trees.Noeud;public class FormatterGD3 extends Formatter {	Rectangle rectParent;	public FormatterGD3(Vector noeuds, Rectangle rectParent) {		super(noeuds);		this.rectParent = rectParent;	}	 public void formatter(Noeud unNoeud) {		setCl(8);		setCh(2);		//posLienRelations(0); // Positionnement horizontal des liens des relations		int p = prof(unNoeud);		demarquer();		//Rectangle parentBounds = getParent().getBounds();		//Rectangle b = new Rectangle(parentBounds.x + 20, parentBounds.y, parentBounds.width, parentBounds.height - 40);		Rectangle b = new Rectangle(rectParent.x + 20, rectParent.y, rectParent.width, rectParent.height - 40);		formatter(unNoeud, b, b.width/(p+1)); // On appelle la methode recursive	}// fin formatterGD3	// Methode formatter recursive de Gauche a droite,	// en tenant compte du plus grand nombre de fils de chaque sous-arbre	void formatter(Noeud n, Rectangle r, int l) {		n.setMarque(true);		int nbFils = 0;		Vector f = n.fils();		n.setPosSup(new Point(r.x, r.y + r.height/2));		for(int i=0; i<f.size(); i++) {			int p = plusGdNbFil((Noeud) f.elementAt(i));			if (p == 0) p = 1;			nbFils = nbFils + p;		}// fin for		int Y = r.y;		Rectangle rec;		for(int i=0; i<f.size(); i++) {			Noeud s = (Noeud)f.elementAt(i);			if(! s.getMarque()) {				int ps = plusGdNbFil(s);				if (ps == 0) ps = 1;				int h = r.height * ps / nbFils;				rec = new Rectangle(r.x + l, Y, l, h);				formatter(s, rec, l);				Y = Y + h;			} //fin if		}// fin for	}// fin formatter recursif}