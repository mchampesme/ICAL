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
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JPanel;
import javax.swing.JTextField;

import lattice.graph.zoom.ZoomEditorInterface;
import lattice.graph.zoom.ZoomInterface;
import lattice.graph.zoom.ZoomViewer;

/**
 * <p>Title: Galicia</p>
 * <p>Description: Galois Lattice Interactive Constructor</p>
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: University of Montreal</p>
 * @author David Grosser
 * @version 1.0
 */
public class ZoomLatticeEditor extends JPanel  implements ZoomEditorInterface {
  // Variables de classes
  static final int QUALITE = 0;
  static final int UPDATE = 1;
  static final int FACTOR_CHANGE = 2;

  // Variables d'instances
  protected ZoomViewer zoomViewer;   // Le canvas rŽduit
  //protected TreeEditor editeur;

  // Pour la gestion des boutons graphiques
  //Image imgQualite, imgUpdate;
  //ImageButton bQualite, bUpdate;
  JPanel panelButton; //Le panel qui contient les boutons
  JTextField zoomFactor; //Le facteur de rŽduction du zoom

  public ZoomLatticeEditor(String nom, ZoomInterface ac) {
    super();
    //zoomViewer = new ZoomLatticeViewer(ac, this);
    zoomViewer = new ZoomViewer(ac, this);
//this.editeur = editeur;
    initAffichage();
  }

  public Dimension getPreferredSize() {
    return new Dimension(170, 165);
  }

  //Constructeurs
          /*public ZoomEditor(String nom, ZoomInterface ac) {
                  super(nom);
                  zoomViewer = new ZoomViewer(ac, this);
  //this.editeur = editeur;
                  initAffichage();
          }*/

  public void initAffichage() {
    //Container c = getContentPane();
    //getContentPane().
    //    setLayout(new BorderLayout(0, 0));
    //setBackground(new Color(70, 70, 100));
    setLayout(new BorderLayout(0, 0));
    setOpaque(false);
    //getContentPane().
    //JPanel p = new JPanel();
    //p.setLayout(new FlowLayout(3));
    //p.add(zoomViewer);
    add(initPanelButton(), BorderLayout.NORTH);
    JPanel p = new JPanel();
    p.setOpaque(false);
    p.add(zoomViewer);
    add(p, BorderLayout.CENTER);
    //add(new JPanel(), BorderLayout.SOUTH);
    //setSize(175, 250);
  }

  protected JPanel initPanelButton() {
    //JButton bQualite = new JButton(rzl.getImage("HighQ2.gif"), true, this, QUALITE);
    //JButton bUpdate = new ImageButton(rzl.getImage("refresh.gif"), false, this, UPDATE);

    panelButton = new JPanel();

    JCheckBox bQualite = new JCheckBox("Quality",  zoomViewer.qualite());
    bQualite.setForeground(Color.white);
    bQualite.addActionListener(new C(QUALITE));
    bQualite.setOpaque(false);
    JButton bUpdate = new JButton(" Update ");
    bUpdate.addActionListener(new C(UPDATE));

    // Le facteur de zoom
    //zoomFactor = new TextFieldChoix("", 5, this, FACTOR_CHANGE);
    zoomFactor = new JTextField("");
    //zoomFactor.setBackground(Color.white);

    panelButton.setOpaque(false);
    //panelButton.setBackground(new Color(10, 210, 240));
    panelButton.setLayout(new FlowLayout(FlowLayout.CENTER, 2, 2));
    //panelButton.setLayout(new BorderLayout());
    //panelButton.setBackground(new Color(10, 210, 240));
    panelButton.add(bQualite);
    panelButton.add(bUpdate);

    //panelButton.add(zoomFactor);


    // Mise en place finale
    //getContentPane().

    updateZoomFactor(zoomViewer.getFactor());
    return panelButton;
  }

  public void setColorPanelButton(Color c) {
    panelButton.setBackground(c);
  }

// MŽthodes d'acc?s
  public void setZoomViewer(ZoomViewer zc) {
    this.zoomViewer = zc;
  }

  public ZoomViewer zoomViewer() {
    return zoomViewer;
  }

  /*	public void dispose() {
                  zoomViewer.dispose();
                  editeur.changeAffZoomViewer2();
                  super.dispose();
          }*/

  public void updateZoomFactor(float f) {
    if(zoomFactor != null) {
      //System.out.println(f);
      String s = Float.toString(f);
      if(s.length() > 5) s = new String(s.substring(0, 5));
      zoomFactor.setText(s);
    }
  }

class C implements ActionListener {

  static final int QUALITE = 0;
  static final int UPDATE = 1;
  static final int FACTOR_CHANGE = 2;

  int action;

  C(int action) {
    this.action = action;
  }

  // Traitement des Žvenements survenant ˆ la barre de Menu
  public void actionPerformed(ActionEvent e) {

      switch(action) {
        case QUALITE: 		zoomViewer.setQualite(! zoomViewer.qualite());
          zoomViewer.refresh1();
          updateZoomFactor(zoomViewer.getFactor());
          break;
        case UPDATE:  		zoomViewer.clearGraphics();
          zoomViewer.refresh1();
          updateZoomFactor(zoomViewer.getFactor());
          break;
        case FACTOR_CHANGE:	Float f = Float.valueOf(zoomFactor.getText());
          zoomViewer.setFactor(f.floatValue());
          zoomViewer.refresh1();
          break;
        default: break;
      }

  }
}

}