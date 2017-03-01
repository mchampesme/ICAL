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

package lattice;

// import Java
import java.applet.Applet;
import java.awt.Button;
import java.awt.Choice;
import java.awt.Color;
import java.awt.Label;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import lattice.gui.graph.LatticeGraphFrame;
import lattice.gui.graph.Example.BigLattice;
import lattice.gui.graph.Example.NestedLattice;
import lattice.gui.graph.Example.SmallLattice1;
import lattice.gui.graph.Example.SmallLattice2;
import lattice.util.structure.ConceptNode;

// import gui
//import lattice.gui.MainController;

/**
 * <p>Title: Galicia</p>
 * <p>Description: Galois Lattice Interactive Constructor</p>
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: University of Montreal</p>
 * @author David Grosser
 * @version 1.0
 */

public class DemoGraphApplet extends Applet implements ActionListener {
  private boolean isStandalone = false;
  private Choice l;
  //Obtenir une valeur de param?tre
  public String getParameter(String key, String def) {
    return isStandalone ? System.getProperty(key, def) :
      (getParameter(key) != null ? getParameter(key) : def);
  }

  //Construire l'applet
  public DemoGraphApplet() {
  }
  //Initialiser l'applet
  public void init() {
    try {
      jbInit();
    }
    catch(Exception e) {
      e.printStackTrace();
    }
  }
  //Initialiser le composant
  private void jbInit() throws Exception {
    //setLookNFeel();
    //new MainController();
    Label label1 = new Label("Lattice Viewer v1.0");
    label1.setForeground(Color.white);
    setBackground(new Color(70, 70, 100));
    Button jb = new Button("Clic to start");
    jb.addActionListener(this);
    add(label1);
    add(jb);
    Label label2 = new Label("developped by D. Grosser");
    label2.setForeground(Color.white);
    add(label2);

    l = new Choice();
    l.add("Normal lattice");
    l.add("Planar lattice");
    l.add("Big lattice");
    l.add("Nested Line Diagram");
    add(l);
  }
  //DŽmarrer l'applet
  public void start() {
  }
  //Arr?ter l'applet
  public void stop() {
  }
  //DŽtruire l'applet
  public void destroy() {
  }
  //Obtenir les informations d'applet
  public String getAppletInfo() {
    return "Galicia v1.0b1 - Galois Lattice Interactive Constructor - Copyright University of Montreal";
  }
  //Obtenir les informations de param?tre
  public String[][] getParameterInfo() {
    return null;
  }

  public void actionPerformed(ActionEvent e) {
    showStatus("Loading classes, please wait...");
    ConceptNode top = null;
    String s = l.getSelectedItem();
    if(s.equals("Normal lattice")) top = (new SmallLattice1()).creer();
    if(s.equals("Planar lattice")) top = (new SmallLattice2()).creer();
    if(s.equals("Big lattice")) top = (new BigLattice()).creer();
    if(s.equals("Nested Line Diagram")) top = (new NestedLattice()).creer();
    showStatus("Generating lattice, please wait...");
    LatticeGraphFrame f = new LatticeGraphFrame(s, top);
    showStatus("Opening lattice viewer");
    f.setLocation(150, 50);
    f.show();
    //f.control.setLocation(650, 50);
    //f.control.show();
  }

  /*private void setLookNFeel() {
          try {
                  UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
          } catch (Exception e) {
                  e.printStackTrace();
          }
	}*/

}