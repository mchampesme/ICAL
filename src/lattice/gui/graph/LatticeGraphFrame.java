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

//import lattice.gui.graph.Exemple.*;
import java.awt.BorderLayout;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.Rectangle;

import javax.swing.JFrame;
import javax.swing.JMenuBar;
import javax.swing.JToolBar;

import lattice.gui.graph.control.LatticeToolBar;
import lattice.gui.graph.control.ZoomLatticeEditor;
import lattice.util.concept.Concept;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.Node;

/**
 *
 * <p>Titre : Lattice</p>
 * <p>Description : Fen?tre interne destinée à manipuler un treillis</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Equipe GELO, Université de Montréal</p>
 * @author David Grosser
 * @version 1.0
 */

public class LatticeGraphFrame extends JFrame {

// La barre de menu
  protected JMenuBar menuBar;


// Le panel de visualisation du treillis
  protected LatticeGraphViewer lgv;

// La barre d'outils
  protected JToolBar toolBar;

// La fen?tre de zoom
  protected ZoomLatticeEditor fZoom;

// Le container
  protected Container content;

  /**
   * Constructeur : titre + top du treillis
   */
  public LatticeGraphFrame(String title, Node<Concept> top) {
    super(title);
    init(top);
  }

  /**
   * Initialisation avec top en param?tre
   */
  public void init(Node<Concept> top) {
    //menuBar = new GraphMenuBar(this);
    //setJMenuBar(menuBar);
    content = this.getContentPane();
    content.setLayout(new BorderLayout(0,0));
    //c.setLayout(new BorderLayout(0, 0));
    //System.out.println(((BorderLayout) c.getLayout()).getHgap());
    //c.add(lgcp, BorderLayout.WEST);
    //setMenuBar(null);
    //c.add(createGraphViewer(), BorderLayout.CENTER);

    lgv = new LatticeGraphViewer();
    content.add(lgv, BorderLayout.CENTER);
    lgv.initLatticeGraphViewer(top);
    //lgv.formatter();
    //c.add(lgv, BorderLayout.CENTER);

    //control = new JFrame("Lattice control");
    //control.getContentPane().add(new LGControlPanel(lgv));
    //setSize(prefSize());
    //show(); // Ouverture de this
    //control.pack();

    //fZoom = new ZoomLatticeEditor("Zoom", lgv);
    //fZoom.setFloatable(true);
    toolBar = new LatticeToolBar(lgv);
    content.add(toolBar, BorderLayout.EAST);
    setSize(getPreferredSize());
    //fZoom.show();

    //f.show(); // Ouverture du panel de control
    //c.add(createGraphViewer());
    //validate();
  }

  /**
   * Calculer la taille englobante du treillis initial
   */
  public Dimension getPreferredSize() {
    Dimension d = lgv.getPreferredSize();
    int h = d.height+20;
    int w = d.width;
    Dimension d2 = toolBar.getPreferredSize();
    int rw = w+d2.width;
    int rh = Math.max(h, d.height);
    if(rw > 850) rw = 850;
    if(rh > 720) rh = 720;
    return new Dimension(rw, rh);
  }


  /**
   * Calculer la taille englobante du treillis initial
   */
/*  public Dimension getMinimumSize() {
    Dimension d = lgv.getMinimumSize();
    int h = d.width;
    int w = d.height;
    Dimension d2 = toolBar.getMinimumSize();
    return new Dimension(w+d2.width, d.height);
  }*/

/*public void setSize(Dimension d) {
  super.setSize(d);
  if(fZoom != null) fZoom.zoomViewer().refresh();
}*/

/**
 * Permet de masquer ou démasquer le zoom Canvas
 */
  public void changeAffZoomViewer() {
    if(fZoom != null) {
      //fZoom.dispose();
      fZoom = null;
      lgv.setZoomViewer(null);
    }
    else {
      fZoom = new ZoomLatticeEditor("Zoom : " + getTitle(), lgv);
      lgv.setZoomViewer(fZoom.zoomViewer());
      //fZoom.setColorPanelButton(defaultColor);
      fZoom.setLocation(getLocationOnScreen().x+getSize().width+10, getLocationOnScreen().y);
      //fZoom.show();
      fZoom.zoomViewer().refresh1();
      fZoom.zoomViewer().setRect(new Rectangle(0, 0, lgv.getSize().width, lgv.getSize().height));
    }
    //if(affichage != null) ((MenuAffichage) affichage).affZoomViewer.changeLabel();
  }

// Gestion PDF
  public void generatePdf() {
    //GraphToPdf gtp = new GraphToPdf();
    //gtp.generate();
  }


}