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

package lattice.gui.graph.magneto;

import java.util.Vector;

import lattice.gui.graph.LatticeNodeGraph;
import lattice.gui.graph.LatticeRelation;
/**
 * <p>Title: Galicia</p>
 * <p>Description: Galois Lattice Interactive Constructor</p>
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: University of Montreal</p>
 * @author David Grosser
 * @version 1.0
 */

public class MagnetableRelation implements Magnetable {

  public LatticeRelation lr; // La relation encapsulŽe
  public int difNbNiveau;    // La diffŽrence de niveau entre l'origine et l'extremitŽ de la relation
  public int rang;           // L'objet magnŽtique est associŽ au i?me rang. Par ex. si diffNbNiveau = 3, 2 objets magntique seront associŽs ˆ la m?me relation, une pour chaqu'un des 2 niveaux intermŽdiaires
  public boolean isMagnetable = true;

  public MagnetableRelation(LatticeRelation lr, int difNbNiveau, int rang) {
    this.lr = lr;
    this.difNbNiveau = difNbNiveau;
    this.rang = rang;
  }

  // Implements Magnetable

// x coord
  public int xCoord() {
    int x = 0;
    int xOrigine = lr.origine().x();
    int xExtremite = lr.extremite().x();
    if(xOrigine > xExtremite) return xExtremite + (rang*(xOrigine - xExtremite))/difNbNiveau;
    else return xOrigine + (rang*(xExtremite - xOrigine))/difNbNiveau;
  }

// y coord
  public int yCoord() {
    int y = 0;
    int yOrigine = lr.origine().y();
    int yExtremite = lr.extremite().y();
    if(yOrigine < yExtremite) return yOrigine + (rang*(yExtremite - yOrigine))/difNbNiveau;
    //else return xOrigine + (rang*(xExtremite - xOrigine))/difNbNiveau;
return 0;
  }

// y coord
  public int zCoord() {
    int z = 0;
    int zOrigine = lr.origine().z();
    int zExtremite = lr.extremite().z();
    if(zOrigine < zExtremite) return zOrigine + (rang*(zExtremite - zOrigine))/difNbNiveau;
    //else return xOrigine + (rang*(xExtremite - xOrigine))/difNbNiveau;
return 0;
  }

// Return Magnetables parents vector if there is relations
  public Vector getParents() {
    return null;
  }

// Return Magnetables children  Vector if there is relations
  public Vector getChildren() {
    return null;
  }

// true if the magnetable object is selected
/*  public boolean isSelected() {
    return false;
  }*/

  /**
   * Return true if the magnetism can move this
   */
  public boolean isMagnetable() {
    return isMagnetable;
  }

  public void setIsMagnetable(boolean b) {
    isMagnetable = b;
  }


// The tension of the magnetable object on X axis
  public double tensionX(boolean b) {
    return 0.0;
  }

// The tension of the magnetable object on Y axis
  public double tensionY(boolean b) {
    return 0.0;
  }

// The tension of the magnetable object on Z axis
  public double tensionZ(boolean b) {
    return 0.0;
  }

// Le facteur de rŽpulsion de cet objet
  public double repulsion() {
    return 0.4;
  }

// Is the Magnetable going to the right
// Used by rotation object in class Magneto
  public boolean goRight() {return true;}

  public void setGoRight(boolean b){}

// Move the magnetable with dx and dy
  public void move(int dx, int dy) {
   int dx2 = dx - ((rang * dx)/difNbNiveau)/4;
    int dx3 = ((rang * dx)/difNbNiveau)/4;
    LatticeNodeGraph lng = ((LatticeNodeGraph) lr.extremite());
    if(lng.isMagnetable()) lng.move(dx2, dy);
    lng = ((LatticeNodeGraph) lr.origine());
    if(lng.isMagnetable()) lng.move(dx3, dy);
  }

  public void move(int dx, int dy, int dz) {

  }

  public int getDifNbNiveau() {
    return difNbNiveau;
  }
  public void setDifNbNiveau(int difNbNiveau) {
    this.difNbNiveau = difNbNiveau;
  }


  public boolean isIsMagnetable() {
    return isMagnetable;
  }

}