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

/**
 * <p>Title: Galicia</p>
 * <p>Description: Galois Lattice Interactive Constructor</p>
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: University of Montreal</p>
 * @author David Grosser
 * @version 1.0
 */

public interface Magnetable {

// x coord
  public int xCoord();

// y coord
  public int yCoord();

  // z coord
  public int zCoord();

// Return Magnetables parents vector if there is relations
  public Vector getParents();

// Return Magnetables children  Vector if there is relations
  public Vector getChildren();

// true if the magnetable object is selected
  public boolean isMagnetable();

// true if the magnetable object is selected
  public void setIsMagnetable(boolean b);

  /**
   * The tension of the magnetable object on X axis
   * b = true : we also consider the starting relationships
   * b = false : we only consider the entrance relationships
   */
  public double tensionX(boolean b);

  /**
   * The tension of the magnetable object on Y axis
   * b = true : we also consider the starting relationships
   * b = false : we only consider the entrance relationships
   */
  public double tensionY(boolean b);

  /**
   * The tension of the magnetable object on Z axis
   * b = true : we also consider the starting relationships
   * b = false : we only consider the entrance relationships
   */
  public double tensionZ(boolean b);

// The repulsion Factor
  public double repulsion();

// Move the magnetable with dx and dy
  public void move(int dx, int dy);

  public void move(int dx, int dy, int dz);

// Is the Magnetable going to the right
// Used by rotation object in class Magneto
  public boolean goRight();

  public void setGoRight(boolean b);
}