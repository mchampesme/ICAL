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

package lattice.graph.trees;/*** IKBS - Editeur de modeles* DŽfinition de la classe RelationSelect* David Grosser - Mars 1997 - IREMIA, UniversitŽ de la RŽunion* Version 1.0* Revu le 7/04/97*/import java.awt.Color;import java.awt.Graphics;import java.awt.Rectangle;// Une relation qui n'est pas encore "terminŽe"public class RelationSelect extends Relation {	int x, y ;	// Constructeur	public RelationSelect(Noeud origine, int x, int y) {		super() ;		this.origine = origine;		this.x = x ;		this.y = y ;	}	public int supGaucheX() {		int o;		o = origine().supGaucheX() ;		if (o > x) return x ;		else return o;	}	public int supGaucheY() {		int o;		o = origine().supGaucheY() ;		if (o > y) return y ;		else return o;	}	public int infDroitX() {		int o;		o = origine().infDroitX() ;		if (o > x) return o ;		else return x;	}	public int infDroitY() {		int o;		o = origine().infDroitY() ;		if (o > y) return o ;		else return y;	}	public int width() {		return infDroitX() - supGaucheX();	}	public int height() {		return infDroitY() - supGaucheY();	}	public void setPos(int a, int b) {		x = a ;		y = b ;	}	public Rectangle rect() {			return new Rectangle(supGaucheX() - widthArrow, supGaucheY() - widthArrow, width() + 2*widthArrow, height() + 2*widthArrow) ;	}/**	* Pour se dessiner en forme droite*/	public void paint1(Graphics g, int xRel, int yRel) {		g.setColor(Color.red) ;		int x1, y1;		if(posLien == 0) {			x1 = origine().infDroitX();			y1 = origine.infDroitY() - origine.height()/2;		}		else {			x1 = origine().supGaucheX() + origine().width()/2;			y1 = origine.infDroitY();		}		g.drawLine(x1, y1, x, y);		if (showArrow) paintArrow(g, x1, y1, x, y);	} // fin paint/**	* Pour se dessiner en escalier*/	public void paint2(Graphics g, int xRel, int yRel) {		g.setColor(Color.red) ;		int x1, y1, x2, y2, x3, y3, x4, y4;		if(posLien == 0) {			x1 = origine().infDroitX(); 						// origine en x			y1 = origine().infDroitY() - origine().height()/2; 	// origine en y			if(decalage2dPoint)  x2 = getDecalage2dPoint();			else x2 = x1 + (x - x1) / 4; // point intermediaire en x			y2 = y1;											// point intermediaire en y			x3 = x2;											// point intermediaire 2 en x			y3 = y + origine.height()/2; // intermediaire 2 en y			x4 = x;						// extremite en x			y4 = y3;											// extremite en y		}		else {//Positionnement vertical des liens			x1 = origine().supGaucheX() + origine().rect2().width/2; 	// origine en x			y1 = origine().infDroitY(); 						// origine en y			x2 = x1;	 										// point intermediaire en x			y2 = y1 + (y - y1) / 4;												// point intermediaire en y			x3 = x;											// point intermediaire 2 en x			y3 = y2; 											// intermediaire 2 en y			x4 = x3;											// extremite en x			y4 = y;						// extremite en y		}		g.drawLine(x1, y1, x2, y2);		g.drawLine(x2, y2, x3, y3);		g.drawLine(x3, y3, x4, y4);		// Dessin de la fleche		if (showArrow) paintArrow(g, x3, y3, x4, y4);	} // fin paint2}