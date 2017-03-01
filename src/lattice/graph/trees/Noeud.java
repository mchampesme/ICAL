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

package lattice.graph.trees;import java.awt.Color;import java.awt.FontMetrics;import java.awt.Graphics;import java.awt.Point;import java.awt.Rectangle;import java.util.Observer;import java.util.Vector;public interface Noeud extends Observer {// Les noeud doivent implémenter Selectable	public void addObserver(Observer o);// Label de l'objet	public String getLabel();	public void setLabel(String s);// Objet visible	public boolean visible();	public void calculDimension(FontMetrics fmObj, FontMetrics fmAtt, FontMetrics fmRel); // Pour calculer la dimension	public void calculDimensionObj(FontMetrics fmObj); // Pour calculer la dimension d'un noeud	public void calculDimensionAtt(FontMetrics fmAtt); // Pour calculer la dimension de la liste d'attributs	public void calculDimensionRel(FontMetrics fmRel); // Pour calculer la dimension des relations d'un noeud	public void setRacine(boolean b);// Le noeud est la racine de l'arbre	public int nbFils();	public Noeud fils(int i);	public Vector fils();	public boolean isFilsVisible(); // Tous les fils sont-ils affichés ?	public boolean sourisDans(int x, int y); // La souris est-elle dans le noeud ?// Pour la gestion de marqueurs	public void setMarque(boolean b);	public boolean getMarque();	public void setMarque2(boolean b);	public boolean getMarque2();// Coordonnées et dimension de l'objet	public void bouge(int x, int y);	public Rectangle rect();	public Rectangle rectRels(); // Rectangle englobant de l'objet et de ses relations	public int height();	public int width();	public int infDroitY();	public int infDroitX();	public int supGaucheX();	public int supGaucheY();// Selection de l'objet        public boolean getSelected();	public void setSelected(boolean b);	public void initColor();	public void showLabelRelations(boolean b);	public void setVisible(boolean b);	public void setActiveNode(boolean b);	public void setAffAttributs(boolean b);	public void setBgColor(Color c);	public void setBgColorAtt(Color c);        public Color bgColor();	public void setLabelColor(Color c);	public void setLabelColorAtt(Color c);	public int x();	public int y();        public double xd();	public double yd();        public int z();        public double zd();	public boolean dansRect(Rectangle r);	public int nbRelationArrive();	public void setPosSup(Point p);	public void setPos(Point p);	public int maxLargeur();	public int maxHauteur();	public int largeur(Noeud n); // largeur d'une relation	public Rectangle rect2();	public Rectangle rect3();	public Attribut dansAttributs(int x, int y);	public int find(Attribut att);// Information	public String getInfo();// Relations	public void addRelationDepart(Relation r);	public void addRelationArrive(Relation r);	public Relation rechRelationArrive(Noeud n);	public void changeFormeRelation(int forme);	public Vector relationArrive();	public Relation relationArrive(int i);	public Vector relationDepart();	public Relation relationDepart(int i);	public void removeRelationDepart(Relation uneRelation);	public void removeRelationArrive(Relation uneRelation);	public void removeRelations(); // Efface toutes les relations	public void removeAttribut(String s); //Efface l'attribut de nom s	public void setShowArrow(boolean b);	public void setPosLien(int pos);	public void addAttribut(Attribut unAttribut);	public Attribut createAttribute();// Attributs	public boolean affAttributs();	public Attribut rechAttribut(String s);	public Attribut rechAttSuivant(String label);	public Attribut rechAttPrecedent(String label);	public AttributsList attributs();// Paint	public void paint(Graphics g, int xRel, int yRel);	public void paintShadow(Graphics g, int xRel, int yRel);	public void paintAtt(Graphics g, int xRel, int yRel);	public void paintAttShadow(Graphics g, int xRel, int yRel);	public void paintRelations(Graphics g, int xRel, int yRel);// Clone	public Object clone();}