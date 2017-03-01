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

package lattice.gui.graph;

// import java
import java.awt.Color;
import java.awt.Component;
import java.awt.Graphics;
import java.awt.Image;
import java.awt.Point;
import java.awt.image.IndexColorModel;
import java.awt.image.MemoryImageSource;
import java.util.Iterator;
import java.util.Vector;
import java.util.List;

import lattice.graph.trees.NodeGraph;
import lattice.graph.trees.Relation;
import lattice.gui.graph.magneto.Magnetable;
import lattice.gui.graph.threeD.ScalableAtom;
import lattice.util.concept.Concept;
import lattice.util.concept.Extent;
import lattice.util.concept.Intent;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.Node;

/**
 * <p>Titre : LatticeNodeGraph : représentation graphique d'un noeud du treillis</p>
 * <p>Description : Les noeuds graphiques du treillis</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : Université de Montréal</p>
 * @author David Grosser
 * @version 1.0
 */

public class LatticeNodeGraph extends NodeGraph implements Comparable, Magnetable, ScalableAtom {

  public Node<Concept> latticeNode; // Le noeud du treillis
  public int niveau = -1;
  public double tensionX, tensionY, tensionZ = Double.MIN_VALUE;
  public boolean isMagnetable = true;
  public boolean goRight = true;

  public LatticeNodeGraph(Node<Concept> n, int x, int y) {
    super(n.toString(), new Point(x, y));
    this.latticeNode = n;
    addIntent();
    addExtent();
    addGenerator();
  }

// Implements Magnetable

/**
 * Return true if the magnetism can move this
 */
  public boolean isMagnetable() {
    return (isMagnetable && (! getSelected()));
  }

  public void setIsMagnetable(boolean b) {
    isMagnetable = b;
  }

// Return Magnetables parents vector if there is relations
  public Vector getParents() {
    return peres();
  }

// Return Magnetables children  Vector if there is relations
  public Vector getChildren() {
    return fils();
  }


  public int xCoord() {
    return x();
  }

  public int yCoord() {
    return y();
  }

  public int zCoord() {
    return z();
  }

  public void move(int dx, int dy) {
    bouge(dx, dy);
  }

  public void move(int dx, int dy, int dz) {
    bouge(dx, dy, dz);
  }

  public boolean isSelected() {
    return getSelected();
  }

  public int getNiveau() {
    return niveau;
  }

  public void setNiveau(int n) {
    this.niveau = n;
  }

  public double repulsion() {
    return 1.0;
  }

  public double tensionX(boolean b) {
    if(tensionX != Double.MIN_VALUE) return tensionX;
    double t = 0;
    double l = 0;
    double lTotale = 0;
    for(int i=0; i<nbRelationArrive(); i++) {
      l += relationArrive(i).origine().xd() - xd();
      lTotale += ((LatticeRelation) relationArrive(i)).longueur();
      //t += Math.cos(dec);
    }
    if(b) for(int j=0; j<nbRelationDepart(); j++) {
      l += relationDepart(j).extremite().xd() - xd();
      lTotale += ((LatticeRelation) relationDepart(j)).longueur();
      //double dec = xd() - relationDepart(j).extremite().xd();
      //t += Math.cos(dec);
    }
    if(b) tensionX = ((nbRelationDepart()+nbRelationArrive())*l / lTotale);
    else tensionX = (nbRelationArrive()*l / lTotale);
    return tensionX;
  }

  public double tensionY(boolean b) {
    if(tensionY != Double.MIN_VALUE) return tensionY;
    double t = 0;
    double l = 0;
    double lTotale = 0;
    for(int i=0; i<nbRelationArrive(); i++) {
      l += relationArrive(i).origine().yd() - yd();
      lTotale += ((LatticeRelation) relationArrive(i)).longueur();
    }
    if(b) for(int j=0; j<nbRelationDepart(); j++) {
      l += relationDepart(j).extremite().yd() - yd();
      lTotale += ((LatticeRelation) relationDepart(j)).longueur();
    }
    if(b) tensionY = ((nbRelationDepart()+nbRelationArrive())*l / lTotale);
    else tensionY = (nbRelationArrive()*l / lTotale);
    return tensionY;
  }

  public double tensionZ(boolean b) {
    if(tensionZ != Double.MIN_VALUE) return tensionZ;
    double t = 0;
    double l = 0;
    double lTotale = 0;
    for(int i=0; i<nbRelationArrive(); i++) {
      l += relationArrive(i).origine().zd() - zd();
      lTotale += ((LatticeRelation) relationArrive(i)).longueur();
      //t += Math.cos(dec);
    }
    if(b) for(int j=0; j<nbRelationDepart(); j++) {
      l += relationDepart(j).extremite().zd() - zd();
      lTotale += ((LatticeRelation) relationDepart(j)).longueur();
      //double dec = xd() - relationDepart(j).extremite().xd();
      //t += Math.cos(dec);
    }
    if(b) tensionZ = ((nbRelationDepart()+nbRelationArrive())*l / lTotale);
    else tensionZ = (nbRelationArrive()*l / lTotale);
    return tensionZ;
  }

public void bouge(int dx, int dy) {
  super.bouge(dx, dy);
  tensionX = Double.MIN_VALUE;
  tensionY = Double.MIN_VALUE;
}

public void bouge(int dx, int dy, int dz) {
  //System.out.println("move dx = "+dx+" dy = "+dy+" dz = "+dz);
  x += (double) dx;
  y += (double) dy;
  z += (double) dz;
  tensionX = Double.MIN_VALUE;
  tensionY = Double.MIN_VALUE;
  tensionZ = Double.MIN_VALUE;
}

  /*public double getTension() {
    return tension;
  }

  public void setTension(double n) {
    this.tension = n;
  }*/

  // Is the Magnetable going to the right
// Used by rotation object in class Magneto
  public boolean goRight() {
    return goRight;
  }

  public void setGoRight(boolean b) {
    this.goRight = b;
  }

  public Node<Concept> getNode() {
    return latticeNode;
  }

  public Concept getConcept() {
    return latticeNode.getContent();
  }

  public Intent getIntent() {
    if(getConcept() != null) return getConcept().getIntent(); //Simplify 
    else return null;
  }

  public Extent getExtent() {
    if(getConcept() != null) return getConcept().getExtent(); // Simplify
    else return null;
  }

  public List getGenerator() {
  	if(getConcept() != null) return getConcept().getGenerator();
  	else return null;
  }

  public void addIntent() {
    //super.addAttribut(lag);
    addAttribut(new LatticeAttributeGraph(this, propToString(false)));
  }

  public void addExtent() {
    addAttribut(new LatticeAttributeGraph(this, propToString(true)));
  }

  public void addGenerator() {
  	String s = affGenerator();
  	if(s != null) addAttribut(new LatticeAttributeGraph(this, s));
  }

	public String affGenerator() {
    	if(getConcept() == null) return null;
    	boolean test = true;
    	String s = new String("G={");
      	Iterator i = getGenerator().iterator();
    	for( ; i.hasNext() ; ) {
    		test = false;
      		s += i.next().toString();
      		if(i.hasNext()) s += ", ";
    	}
    	s += "}";
    	if(test) return null;
    	return s;
  	}

  public void setSelected(boolean b) {
    super.setSelected(b);
    //setAffAttributs(b);
  }

  // true : extension, false : intension
  public String propToString(boolean b) {
    if(getConcept() == null) return new String("");
    Iterator i = null;
    String s = null;
    if(b) {
      s = new String("E={");
      i = getExtent().iterator();
    }
    else {
      s = new String("I={");
      i = getIntent().iterator();
    }
    for( ; i.hasNext() ; ) {
      s += i.next().toString();
      if(i.hasNext()) s += ", ";
    }
    s += "}";
    
    return s;
  }

  public int nbRelations() {
    return nbRelationArrive()+nbRelationDepart();
  }

  /**
   * La relation d'ordre est donnée par la coordonnées x
   */
  public int compareTo(Object o) {
    LatticeNodeGraph lng = (LatticeNodeGraph) o;
    if(lng.x() < this.x()) return 1;
    if((lng.x() == this.x())&&(lng.nbRelations()>nbRelations())) return 1;
    return -1;
  }

  /**
   * Calcul de la longeur totale des relations
   */
  public double longueurRelations() {
    double longueur = 0;
    Relation r;
    for(int i=0; i<nbRelationArrive(); i++) {
      r = relationArrive(i);
      longueur += ((LatticeRelation) r).longueur();
    }
    for(int j=0; j<nbRelationDepart(); j++) {
      r = relationDepart(j);
      longueur += ((LatticeRelation) r).longueur();
    }
    return longueur;
  }

  /**
   * Dessin des relations
   * * Surcharge
   * Vraiment en plus pour faire joli et s'amuser un peu !
   */
  public void paintRelations(Graphics g, int xRel, int yRel) {
    if(! IS_COLORED) super.paintRelations(g, xRel, yRel);
    else {
      if (c == null) {
        c = new Color[nbRelationDepart() + nbRelationArrive()];
        double d = Math.random();
        for(int j = 0; j<nbRelationDepart() + nbRelationArrive(); j++) {
          c[j] = randomColor(d, j);
        }
      }
      int [] xPoints = new int[3];
      int [] yPoints = new int[3];
      xPoints[0] = supGaucheX() + width()/2 + xRel;
      yPoints[0] = supGaucheY() + yRel;
      for(int j = 0; j<nbRelationDepart()-1; j++) {
        xPoints[1] = relationDepart(j).extremite().supGaucheX() + width()/2 + xRel;
        yPoints[1] = relationDepart(j).extremite().supGaucheY() + yRel;
        xPoints[2] = relationDepart(j+1).extremite().supGaucheX() + width()/2 + xRel;
        yPoints[2] = relationDepart(j+1).extremite().supGaucheY() + yRel;
        g.setColor(c[j]);
        g.fillPolygon(xPoints, yPoints, 3);
      }
      for(int j = 0; j<nbRelationArrive()-1; j++) {
        xPoints[1] = relationArrive(j).origine().supGaucheX() + width()/2 + xRel;
        yPoints[1] = relationArrive(j).origine().supGaucheY() + yRel;
        xPoints[2] = relationArrive(j+1).origine().supGaucheX() + width()/2 + xRel;
        yPoints[2] = relationArrive(j+1).origine().supGaucheY() + yRel;
        g.setColor(c[j+nbRelationDepart()]);
        g.fillPolygon(xPoints, yPoints, 3);
      }
    }
    //}
    //super.paintRelations(g, xRel, yRel);
  }

  private Color[] c;
// Ppour s'amuser avec les couleurs
  public static boolean IS_COLORED = false;

  public Color randomColor(double d, int j) {
    double f = Math.random();
    int col = 50 + (int) (f * 200.0);
    if(d < 0.2) return new Color(0, 0, col);
    if(d < 0.4) return new Color(0, col, 0);
    if(d < 0.6) return new Color(col, 0, 0);
    if(d < 0.8) return new Color(col, col, 0);
    return new Color(col, 0, col);
  }

// Pour la gestion de la vue 3D (implemente ScaleableAtom)
  //private double z=0;

  private static Component applet;
  private static byte[] data;
  private final static int R = 40;
  private final static int hx = 15;
  private final static int hy = 15;
  private final static int bgGrey = 192;
  private static int maxr;

  private int Rl;
  private int Gl;
  private int Bl;
  private double Sf;

  private Image balls[];

  static {
    data = new byte[R * 2 * R * 2];
    int mr = 0;
    for (int Y = 2 * R; --Y >= 0;) {
      int x0 = (int) (Math.sqrt(R * R - (Y - R) * (Y - R)) + 0.5);
      int p = Y * (R * 2) + R - x0;
      for (int X = -x0; X < x0; X++) {
        int x = X + hx;
        int y = Y - R + hy;
        int r = (int) (Math.sqrt(x * x + y * y) + 0.5);
        if (r > mr)
          mr = r;
        data[p++] = r <= 0 ? (byte) 1 : (byte) r;
      }
    }
    maxr = mr;
  }
  public static void setApplet(Component app) {
    applet = app;
  }
    /*ScaleableAtom(int Rl, int Gl, int Bl, double Sf) {
        this.Rl = Rl;
        this.Gl = Gl;
        this.Bl = Bl;
        this.Sf = Sf;
    }*/

  public void init3D(int Rl, int Gl, int Bl, double Sf) {
    this.Rl = Rl;
    this.Gl = Gl;
    this.Bl = Bl;
    this.Sf = Sf;
  }

  public boolean Exist() {
    if (Sf==0.0)
      return false;
    else
      return true;
  }
  public int blend(int fg, int bg, float fgfactor) {
    return (int) (bg + (fg - bg) * fgfactor);
  }
  public void Setup(int nBalls) {
    balls = new Image[nBalls];
    byte red[] = new byte[256];
    red[0] = (byte) bgGrey;
    byte green[] = new byte[256];
    green[0] = (byte) bgGrey;
    byte blue[] = new byte[256];
    blue[0] = (byte) bgGrey;
    for (int r = 0; r < nBalls; r++) {
      float b = (float) (r+1) / nBalls;
      for (int i = maxr; i >= 1; --i) {
        float d = (float) i / maxr;
        red[i] = (byte) blend(blend(Rl, 255, d), bgGrey, b);
        green[i] = (byte) blend(blend(Gl, 255, d), bgGrey, b);
        blue[i] = (byte) blend(blend(Bl, 255, d), bgGrey, b);
      }
      IndexColorModel model = new IndexColorModel(8, maxr + 1,
          red, green, blue, 0);
      balls[r] = applet.createImage(
          new MemoryImageSource(R*2, R*2, model, data, 0, R*2));
    }
  }
  public void paint(Graphics gc, int x, int y, int r) {
    Image ba[] = balls;
    if (ba == null) {
      Setup((int)(16*Sf));
      ba = balls;
    }
    r=(int)(r*Sf);
    Image i = ba[r];
    int size = 10 + r;
    gc.drawImage(i, x - (size >> 1), y - (size >> 1), size, size, applet);
  }



}