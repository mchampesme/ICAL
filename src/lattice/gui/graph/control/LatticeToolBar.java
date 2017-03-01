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

package lattice.gui.graph.control;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.GridBagLayout;
import java.awt.Image;
import java.awt.Insets;

import javax.swing.ImageIcon;
import javax.swing.JLabel;
import javax.swing.JToolBar;

import lattice.graph.utils.IkbsPanel;
import lattice.gui.graph.LatticeGraphViewer;
import lattice.gui.util.ResourceManager;
/**
 * <p>Title: Galicia</p>
 * <p>Description: Galois Lattice Interactive Constructor</p>
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: University of Montreal</p>
 * @author David Grosser
 * @version 1.0
 */

public class LatticeToolBar extends JToolBar {
  /**
   * Le viewer de treillis
   */
  protected LatticeGraphViewer lgv;
  /**
   * La panel de zoom
   */
  protected ZoomLatticeEditor zle;

  /**
   * La barre de control
   */
  protected LGControlPanel lgcp;

// Constructeur
  public LatticeToolBar(LatticeGraphViewer lgv) {
    super("Control", JToolBar.VERTICAL);
    this.lgv = lgv;
    try {
      jbInit();
    }
    catch(Exception e) {
      e.printStackTrace();
    }
  }

  private void jbInit2() throws Exception {
    //setLayout(new FlowLayout(FlowLayout.CENTER, 3, 3));
    //setLayout(new BorderLayout(2, 2));
    setLayout(new FlowLayout(0));
    //IkbsPanel p = new IkbsPanel();
    setOpaque(false);
    //setLayout(new GridBagLayout());
    //p.initGridBagConstraint();
    //p.c.insets=new Insets(0, 0, 0, 0);
    setBackground(new Color(50, 50, 70));
    setBorderPainted(true);
    setFloatable(true);
    setOrientation(JToolBar.VERTICAL);
    zle = new ZoomLatticeEditor("Control", lgv);
    //p.xyPosition(p, zle, 0, 0, 1);
    add(zle);
    //add(zle, BorderLayout.NORTH);
    //control = new JFrame("Lattice control");
    lgcp = new LGControlPanel(lgv);
    //lgcp.pack();
    //control.getContentPane().add(lgcp);
    //p.xyPosition(p, lgcp, 0, 1, 1);
    add(lgcp);
    //add(p, BorderLayout.NORTH);

    // Le label Galicia
    // -- Comment Cyril -- Image i = getToolkit().createImage("ressources/GaliciaPetit.png");
	Image i = getToolkit().createImage(ResourceManager.getGaliciaMinImgURL());
    //JLabel jGalicia = new JLabel(new ImageIcon("ressources/"+"GaliciaPetit.png"));
    JLabel jGalicia = new JLabel(new ImageIcon(i));
    //JLabel jGalicia = new JLabel("Galicia v1.0b1");
    jGalicia.setOpaque(false);
    jGalicia.setToolTipText("Galicia Lattice Viewer Developped by David Grosser");
    add(jGalicia);
  }
  private void jbInit() throws Exception {
    //setLayout(new FlowLayout(FlowLayout.CENTER, 3, 3));
    //setLayout(new BorderLayout(2, 2));
    setLayout(new BorderLayout(0, 0));
    IkbsPanel p = new IkbsPanel();
    p.setOpaque(false);
    p.setLayout(new GridBagLayout());
    p.initGridBagConstraint();
    p.c.insets=new Insets(0, 0, 0, 0);
    setBackground(new Color(50, 50, 70));
    setBorderPainted(true);
    setFloatable(true);
    setOrientation(JToolBar.VERTICAL);
    zle = new ZoomLatticeEditor("Control", lgv);
    p.xyPosition(p, zle, 0, 0, 1);
    //add(zle, BorderLayout.NORTH);
    //control = new JFrame("Lattice control");
    lgcp = new LGControlPanel(lgv);
    //lgcp.pack();
    //control.getContentPane().add(lgcp);
    p.xyPosition(p, lgcp, 0, 1, 1);
    add(p, BorderLayout.NORTH);

    // Le label Galicia
    //Image i = getToolkit().createImage("GaliciaPetit.png");
    
    
    //-- Cyril Comment -- JLabel jGalicia = new JLabel(new ImageIcon("ressources/"+"GaliciaPetit.png"));
	JLabel jGalicia = new JLabel(new ImageIcon(ResourceManager.getGaliciaMinImgURL()));

    //JLabel jGalicia = new JLabel("Galicia v1.0b1");
    jGalicia.setOpaque(false);
    jGalicia.setToolTipText("Galicia Lattice Viewer Developped by David Grosser");
    add(jGalicia, BorderLayout.SOUTH);

    //setAlignmentX(RIGHT_ALIGNMENT);
    //add(lgcp, BorderLayout.CENTER);
    //setSize(prefSize());
    //show(); // Ouverture de this
    //control.pack();
  }

  public Dimension getPreferredSize() {
    setOrientation(JToolBar.VERTICAL);
    //System.out.println(getOrientation());
    return new Dimension(180, 600);
  }

/*  public Dimension getMinimumSize() {
  setOrientation(JToolBar.VERTICAL);
  //System.out.println(getOrientation());
  return new Dimension(180, 600);
  }*/

}