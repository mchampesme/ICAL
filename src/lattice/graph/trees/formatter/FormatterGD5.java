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

package lattice.graph.trees.formatter;// import ikbs.tools.treesimport java.awt.Point;import java.awt.Rectangle;import java.util.Vector;import lattice.graph.trees.Noeud;public class FormatterGD5 extends Formatter {	Rectangle rectParent;	public FormatterGD5(Vector noeuds, Rectangle rectParent) {		super(noeuds);		this.rectParent = rectParent;	}	public void formatter(Noeud unNoeud) {		//posLienRelations(0); // Positionnement horizontal des liens des relations		demarquer();		int p = prof(unNoeud);		int Y, h;		//Rectangle parentBounds = getParent().getBounds();		//Rectangle b = new Rectangle(parentBounds.x + 20, parentBounds.y, parentBounds.width, parentBounds.height - 40);		Rectangle b = new Rectangle(rectParent.x + 20, rectParent.y, rectParent.width, rectParent.height - 40);		int l = b.width/(p+1) ;		int l2 = b.x;		demarquer2();		Vector fils;		for(int i = 0; i<=p; i++) {// boucle par niveau			Y = b.y;			fils = fils(unNoeud, i);			if (fils.size() != 0) {				h = b.height/fils.size();				for (int j = 0; j < fils.size(); j++) {					((Noeud) fils.elementAt(j)).setPosSup(new Point(l2, Y + h/2)) ;					Y = Y + h;				}// fin for j			}//fin if		l2 = l2 + l;		} // fin for i	}// fin formatterGD5}