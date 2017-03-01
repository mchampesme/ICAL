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

package lattice.graph.trees;import java.awt.Color;import java.awt.Dimension;import java.awt.Graphics;import java.awt.Point;import java.awt.Rectangle;import java.util.Observable;/**	* IKBS tools - Package graphique pour la gestion d'arbres et de graphes	* Définition de la classe composant, sous classe de Object	* superclass des composants graphiques d'IKBS	* @author David Grosser	* @date Mars 1997	* @copyright IREMIA, Université de la Réunion	* Version 1.0	* @since 4 avril 2000*/public abstract class Composant extends Observable {// Variables statiques (communes à tous les composants	protected static Dimension shadowSize = new Dimension(2, 2); // Le décalage en x et en y de l'ombre portée	//protected static Color shadow_color = new Color(80, 80, 80);	//protected static Color shadow_color = new Color(102, 102, 204);	//protected static Color shadow_color = new Color(204, 51, 151);	protected static Color cible_color = Color.red;	protected static Color shadow_color = new Color(102, 102, 204);// Variables d'instances/**	* Label du composant*/	protected String label;/**	* Le composant doit-il ?tre affiché ?*/	protected boolean show = true;/**	* Largeur (en pixel) du label, pour ne pas avoir à le calculer à chaque fois que nécessaire.	* Calculé par la méthode calculDimension*/	protected int widthLabel;/**	* hauteur (en pixel) du label, pour ne pas avoir à le calculer à chaque fois que nécessaire.	* Calculé par la méthode calculDimension*/	protected int heightLabel;/**	* Couleur du label et couleur du fond*/	protected Color labelColor, bgColor;/**	* Position du composant*/	protected double x, y, z;/**	* Dimension du composant*/	protected Dimension dimension = new Dimension(100, 100);// Constructeurs	Composant() {		super();	}	Composant(String nom) {		super();		label = nom;	}// Méthodes d'acc?s	public String getLabel() { return label; }	public void setLabel(String l) { label = l; }	public boolean showed() {return show;}	public void showLabel() {show = true;}	public void hideLabel() {show = false; }	public int widthLabel() {return widthLabel;}	public int heightLabel() {return heightLabel;}	public void setWidthLabel(int w) {widthLabel = w;}	public void setHeightLabel(int h) {heightLabel = h;}	public Color labelColor() {return labelColor;}	public void setLabelColor(Color c) {labelColor = c;}	public Color bgColor() {return bgColor;}	public void setBgColor(Color c) {bgColor = c;}	public Point pos() { return new Point((int) x, (int) y); }	public int x() { return (int) x; }	public void setX(int x) {this.x = (double) x ;}	public int y() { return (int) y; }	public void setY(int y) {this.y = (double) y ;}        public void setX(double x) {this.x = x;}        public void setY(double y) {this.y = y;}	public double xd() { return x;}	public double yd() { return y;}        public int z() { return (int) z;}        public double zd() { return z;}        public void setZ(double z) {this.z = z;}        public void setZ(int z) {this.z = (double) z;}	public void setPos(Point p) {x = (double) p.x; y = (double) p.y; }	public void setPos(int x, int y) {this.x = (double) x; this.y = (double) y;}	public void setPos(double x, double y) {this.x = x; this.y = y;}	public Dimension dimension() { return dimension; }	public void setDimension(Dimension dim) { dimension = dim; }	public int height() { return dimension.height; }	public void setHeight(int h) { dimension.height = h; }	public int width() { return dimension.width; }	public void setWidth(int w) { dimension.width = w;}	public abstract Rectangle rect();/**	* Retourne true si le clic a été effectué dans la fen?tre*/	public boolean sourisDans(int x, int y) {		return rect().contains(x, y) ;	}	public boolean dansRect(Rectangle r) {		return rect().intersects(r) ;	}	public String getInfo() {		return getLabel();	}	public String toString() {		return getLabel();	}	public void paintShadow(Graphics g, int xRel, int yRel) {}}// fin classe Composant