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

import lattice.util.structure.ConceptNode;

/**
 * <p>Title: Galicia</p>
 * <p>Description: Galois Lattice Interactive Constructor</p>
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: University of Montreal</p>
 * @author David Grosser
 * @version 1.0
 */

public class NestedLattice extends AbstractExempleLattice {

  public NestedLattice() {
  }

  public ConceptNode creer() {
    ExampleNode top = new ExampleNode(1);
    ExampleNode bottom = new ExampleNode(26);

    ExampleNode c2 = new ExampleNode(2);
    ExampleNode c3 = new ExampleNode(3);
    ExampleNode c4 = new ExampleNode(4);
    ExampleNode c5 = new ExampleNode(5);
    ExampleNode c6 = new ExampleNode(6);
    ExampleNode c7 = new ExampleNode(7);
    ExampleNode c8 = new ExampleNode(8);
    ExampleNode c9 = new ExampleNode(9);
    ExampleNode c10 = new ExampleNode(10);
    ExampleNode c11 = new ExampleNode(11);
    ExampleNode c12 = new ExampleNode(12);
    ExampleNode c13 = new ExampleNode(13);
    ExampleNode c14 = new ExampleNode(14);
    ExampleNode c15 = new ExampleNode(15);
    ExampleNode c16 = new ExampleNode(16);
    ExampleNode c17 = new ExampleNode(17);
    ExampleNode c18 = new ExampleNode(18);
    ExampleNode c19 = new ExampleNode(19);
    ExampleNode c20 = new ExampleNode(20);
    ExampleNode c21 = new ExampleNode(21);
    ExampleNode c22 = new ExampleNode(22);
    ExampleNode c23 = new ExampleNode(23);
    ExampleNode c24 = new ExampleNode(24);
    ExampleNode c25 = new ExampleNode(25);

    top.addChild(c2);
    top.addChild(c3);
    top.addChild(c4);
    c2.addChild(c5);
    c2.addChild(c6);
    c2.addChild(c7);
    c3.addChild(c8);
    c3.addChild(c9);
    c3.addChild(c10);
    c4.addChild(c11);
    c4.addChild(c12);
    c4.addChild(c13);

    c5.addChild(c14);
    c6.addChild(c15);
    c7.addChild(c16);
    c8.addChild(c17);

    c9.addChild(c18);
    c10.addChild(c19);
    c11.addChild(c20);
    c12.addChild(c21);
    c13.addChild(c22);

    c14.addChild(c23);
    c15.addChild(c23);
    c16.addChild(c23);

    c17.addChild(c24);
    c18.addChild(c24);
    c19.addChild(c24);

    c20.addChild(c25);
    c21.addChild(c25);
    c22.addChild(c25);

    c23.addChild(bottom);
    c24.addChild(bottom);
    c25.addChild(bottom);

    c6.addChild(c14);
    c7.addChild(c15);
    c8.addChild(c16);
    c9.addChild(c17);
    c10.addChild(c18);
    c11.addChild(c19);
    c12.addChild(c20);
    c13.addChild(c21);
    c2.addChild(c8);
    c17.addChild(c23);
    c19.addChild(c25);

    return top;
  }
}