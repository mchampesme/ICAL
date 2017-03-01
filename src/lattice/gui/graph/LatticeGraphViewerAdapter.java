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

/**
 * <p>Titre : Lattice</p>
 * <p>Description : Manipulation des treillis</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : Université de Montréal</p>
 * @author David Grosser
 * @version 1.0
 */

package lattice.gui.graph;

 
import java.awt.event.InputEvent;
import java.awt.event.MouseEvent;

import lattice.graph.trees.Selectable;
import lattice.graph.trees.event.ActionGraphViewerAdapter;


// added by Amine
import lattice.io.rasterizer.TranscoderView;

/**
 * <p>Titre : Lattice</p>
 * <p>Description : Manipulation des treillis</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : Université de Montréal</p>
 * @author David Grosser
 * @version 1.0
 */

public class LatticeGraphViewerAdapter extends ActionGraphViewerAdapter {
    LatticeGraphViewer lgvOwner;
    

  public LatticeGraphViewerAdapter(LatticeGraphViewer graphEditor)  {
    super(graphEditor);
    lgvOwner=graphEditor;
  }

  protected void canvasClicked(int x, int y, MouseEvent e) {
    if(e.getButton()==MouseEvent.BUTTON3){
    	TranscoderView tView = new TranscoderView(lgvOwner);
      	tView.display(e);
    }
    else {
      //((LatticeGraphViewer) graphEditor).modAff();
      graphEditor.doSelected(null);
      graphEditor.dragMode();
    }
  }



  public void mousePressed(MouseEvent e) {
    if(! ((LatticeGraphViewer) graphEditor).getThreeD()) 
    	super.mousePressed(e);
    else
      ((LatticeGraphViewer) graphEditor).l3D.mouseDown(e);
  }

  protected void noeudClicked(int x, int y, MouseEvent e) {
    switch(e.getModifiers()) {
      case SHIFT: // touche shift pressŽe : deplacement du sous arbre
        //graphEditor.doSelected((Selectable) graphEditor.noeuds(index));
        graphEditor.moveTree(index());
        break;
      case InputEvent.SHIFT_MASK:
        //graphEditor.doSelected((Selectable) graphEditor.noeuds(index));
        graphEditor.moveTree(index());
        break;
      case META: // touche shift pressŽe : deplacement du sous arbre
        //graphEditor.doSelected((Selectable) graphEditor.noeuds(index));
        graphEditor.changeAffAttributs();
        break;
      case InputEvent.META_MASK:
        //graphEditor.doSelected((Selectable) graphEditor.noeuds(index));
        graphEditor.changeAffAttributs();
        break;
      default:
        graphEditor.doSelected((Selectable) graphEditor.noeuds(index));
      graphEditor.selectNode(index());
      break;
    }
  }
}