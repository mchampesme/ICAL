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

// import java.awt
import java.awt.event.KeyEvent;

import lattice.graph.trees.Relation;
import lattice.graph.trees.event.FormatKeyListener;

/**
 * <p>Titre : Lattice</p>
 * <p>Description : Manipulation des treillis</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : Université de Montréal</p>
 * @author David Grosser
 * @version 1.0
 */

public class FormatKeyLatticeListener extends FormatKeyListener {

  public FormatKeyLatticeListener(LatticeGraphViewer lgv) {
    super(lgv);
  }

	public void keyPressed(KeyEvent e) {
		//System.out.println(e);
		switch(e.getKeyCode()) {

//      public static final int FORMATTER_GD  = 0;
//	public static final int FORMATTER_GD2 = 1;
//	public static final int FORMATTER_GD3 = 2;
//	public static final int FORMATTER_GD4 = 3;
//	public static final int FORMATTER_GD5 = 4;
//	public static final int FORMATTER_HB  = 5;
		case KeyEvent.VK_F1: canvas.setFormatter(LatticeGraphViewer.FORMATTER_HB_LATTICE); break;
		case KeyEvent.VK_F2: canvas.setFormatter(LatticeGraphViewer.FORMATTER_HB_LATTICE2); break;
		case KeyEvent.VK_F3: canvas.setFormatter(LatticeGraphViewer.FORMATTER_HB_LATTICE3); break;
		//case KeyEvent.VK_F4: ((LatticeGraphViewer) canvas).magnet(); break;
		case KeyEvent.VK_F5: canvas.changeFormeRelation(Relation.FORME_DROITE); break;
		case KeyEvent.VK_F6: canvas.changeFormeRelation(Relation.FORME_ESCALIER); break;
		case KeyEvent.VK_F7: canvas.setShowArrow(! canvas.getShowArrow()); break;
		case KeyEvent.VK_F8: LatticeNodeGraph.IS_COLORED = ! LatticeNodeGraph.IS_COLORED; canvas.repaint(); break;
		case KeyEvent.VK_F9: canvas.ZM(); break;
		case KeyEvent.VK_F10: canvas.ZP(); break;
		case KeyEvent.VK_F11: canvas.activeTextRelations(); break;
		case KeyEvent.VK_F12: canvas.desactiveTextRelations(); break;
		default : break;
		}// fin switch
	}// fin keyTyped

}// fin classe FormatKeyListener