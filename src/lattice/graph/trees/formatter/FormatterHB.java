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

package lattice.graph.trees.formatter;import java.awt.Point;import java.util.Vector;import lattice.graph.trees.Noeud;public class FormatterHB extends Formatter {	public FormatterHB(Vector noeuds) {		super(noeuds);	}	public void formatter(Noeud unNoeud) {		setCl(2);		setCh(25);		//posLienRelations(1); // Positionnement vertical des liens des relations		demarquer() ;		demarquer2() ;		Vector v = feuilles(unNoeud) ;		demarquer2() ;		int l = ch() ;		// Positionnement en X des feuilles		Noeud uneFeuille;		Vector peres;		for(int i=0; i<v.size(); i++) {			uneFeuille = (Noeud) v.elementAt(i) ;			uneFeuille.setPosSup(new Point(l, uneFeuille.y()));//marquage1			uneFeuille.setMarque(true) ;			//l = l + uneFeuille.rect().width + ch();			l = l + uneFeuille.rect().width + cl();		} 		for(int i=0; i<v.size(); i++) { 			uneFeuille = (Noeud) v.elementAt(i) ; 			peres = peres(uneFeuille) ; 			for(int j=0; j<peres.size(); j++) 				positionneXPeres((Noeud) peres.elementAt(j)) ; 		}		positionneY(unNoeud, ch()) ;		// Affichage dynamique (plus lent) ou statique		//if(dynamique) positionneDynamique(noeudRacine()) ;		//else {			positionne(unNoeud) ;		//}	}// fin formatterHB}