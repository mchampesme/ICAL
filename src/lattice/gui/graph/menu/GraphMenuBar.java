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

package lattice.gui.graph.menu;

// import java
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;

import lattice.gui.graph.LatticeGraphFrame;

/**
 * <p>Title: Galicia</p>
 * <p>Description: Galois Lattice Interactive Constructor</p>
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: University of Montreal</p>
 * @author David Grosser
 * @version 1.0
 */

public class GraphMenuBar extends JMenuBar implements ActionListener {

  LatticeGraphFrame lgf;

  public GraphMenuBar(LatticeGraphFrame lgf) {
    this.lgf = lgf;
    add(initMenuFile());
    add(initMenuDisplay());
  }

  public JMenu initMenuFile() {
    // File
    JMenu file = new JMenu("File");
    JMenuItem open = new JMenuItem("Open");
    file.add(open);
    JMenuItem save = new JMenuItem("Save");
    file.add(save);
    JMenuItem pdf = new JMenuItem("Save as PDF");
    pdf.addActionListener(this);
    file.add(pdf);
    file.addSeparator();
    JMenuItem close = new JMenuItem("Close");
    file.add(close);
    return file; // Ajoute à la barre de menu le menu file
  }

  public JMenu initMenuDisplay() {
    JMenu display = new JMenu("Display");
    display.add(createPoliceMenu(this));
    return display;
    //MenuDisplay md = new MenuDisplay(lgf);
    //add(md);
  }

  /**
   * Créer une liste des polices existantes
   */
  protected JMenu createPoliceMenu(ActionListener listener) {
          String polices[] = getToolkit().getFontList();
          JMenu police = new JMenu("Fonts");
          for(int i=0; i<polices.length; i++) {
                  JMenuItem m = new JMenuItem(polices[i]);
                  m.addActionListener(listener);
                  police.add(m);
          }
          return police;
        }

  public void actionPerformed(ActionEvent e) {
    lgf.generatePdf();
  }


}