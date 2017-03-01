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

package lattice.graph.trees;/********************************************************************* ikbs.Graphics : MenuList, pour la gestion des menus				** DŽfinition de la classe MenuList extends AttributsList			** David Grosser - fŽvrier 1998 - IREMIA, UniversitŽ de la RŽunion	** Version 1.0														** 3/02/98															**********************************************************************/import java.awt.Color;import java.awt.FontMetrics;import java.awt.Graphics;import java.awt.Rectangle;public class MenuList extends ComposantList {	Noeud noeud; // Le noeud sur lequel on a cliquŽ	int cl = 5;	int ch = 1;	int hauteur = 0;	// Constructeurs	MenuList(Noeud unNoeud) {		super();		noeud = unNoeud;		init2();	}	// Initialisation	void init2() {		setLabelColor(Color.black);		setBgColor(new Color(210, 210, 210));		setWidth(0);		setHeight(0);	}	// MŽthodes d'acc?s	public String item(int i) {return (String) liste.elementAt(i);}	public void remove(String nom) {		liste.removeElementAt(find(nom));	}	public int find(String nom) {		for(int i = nbElement() - 1; i>=0; i--)		{			if(nom == item(i)) return i;		}		return -1;	}// fin find}	// MŽthodes// Calcul la largeur et la hauteur du Menu	public void calculDimension(FontMetrics fm) {	  	if(nbElement() != 0) {	  		hauteur = fm.getHeight();			int indexMax = -1;			int maxWidth = 0;			for(int i = 0; i<nbElement(); i++) {				if (maxWidth < fm.stringWidth(item(i))) {					maxWidth = fm.stringWidth(item(i));					indexMax = i;				}			}// fin for			setWidthLabel(maxWidth);			setHeightLabel(hauteur * nbElement());			setWidth(widthLabel()+2*cl);			setHeight(heightLabel()+ nbElement() * ch + ch + fm.getAscent());		}	}// x et y reprŽsentent les coordonnŽes du clic	public Rectangle rect(int x, int y) {		setPos(x, y);		return new Rectangle(x, y, width(), height());	}	public Rectangle rect() {		return new Rectangle(0, 0, width(), height());	}	// Pour dessiner	public void paint(Graphics g, FontMetrics fm) {		g.setColor(bgColor());		g.fill3DRect(x(), y(), width(), height(), true);		g.setColor(labelColor());		int X = x() + cl;		int Y = y() + ch + hauteur;		for(int i=0; i<nbElement(); i++) {			g.drawString(item(i), X, Y);			Y = Y + hauteur + ch;		}	}//fin paint		// Pour dessiner	public void paint(Graphics g, FontMetrics fm, int xRel, int yRel) {		g.setColor(bgColor());		g.fill3DRect(x(), y(), width(), height(), true);		g.setColor(labelColor());		int X = x() + cl;		int Y = y() + ch + hauteur;		for(int i=0; i<nbElement(); i++) {			g.drawString(item(i), X, Y);			Y = Y + hauteur + ch;		}	}//fin paint}// fin classe MenuList