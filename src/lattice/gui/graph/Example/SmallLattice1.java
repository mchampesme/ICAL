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

package lattice.gui.graph.Example;

import java.util.Vector;

import lattice.util.structure.ConceptNode;

/**
 * <p>Title: Galicia</p>
 * <p>Description: Galois Lattice Interactive Constructor</p>
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: University of Montreal</p>
 * @author David Grosser
 * @version 1.0
 */

public class SmallLattice1 extends AbstractExempleLattice {

  public SmallLattice1() {
  }

  public ConceptNode creer() {
    Vector vNode = new Vector();
    vNode.add("top,7,8,9");
    vNode.add("7,10");
    vNode.add("8,1,11");
    vNode.add("9,10,1,11,5");
    vNode.add("10,12,6");
    vNode.add("1,0");
    vNode.add("11,12,0");
    vNode.add("5,6,3");
    vNode.add("12,bottom");
    vNode.add("6,4");
    vNode.add("3,10,4");
    vNode.add("0,bottom");
    vNode.add("4,bottom");
	return creer(vNode);
  }
}
