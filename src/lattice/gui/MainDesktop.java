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

package lattice.gui;

// import Swing
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Image;
import java.net.URL;

import javax.swing.JScrollPane;

import lattice.gui.util.ResourceManager;

/**
 * <p>Titre : Lattice</p>
 * <p>Description : Manipulation des treillis</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : Université de Montréal</p>
 * @author David Grosser
 * @version 1.0
 */

public class MainDesktop extends JScrollPane {

  
  //-- Cyril Comment -- public static final String bgPicturePath = "ressources/Galicia.png";
  public static final URL bgPicturePath = ResourceManager.getGaliciaBigImgURL();


  //public Color bgColor = Color.white;
  public Color bgColor = new Color(200, 200, 220);
  public Image backgroundPicture;

  public MainDesktop() {
    super();
    //setDragMode(OUTLINE_DRAG_MODE);
    setBackground(bgColor);
    initBgPicture();


  }

  public void initBgPicture() {
    try {
      backgroundPicture = getToolkit().getImage(bgPicturePath);
    }
    catch(Exception e) {System.out.println(e);}
  }

/*  public Desktop(Image img) {
    this();
    backgroundPicture = img;
  }*/

  public void paint(Graphics g) {
    super.paint(g);
    if(backgroundPicture != null) {
      Dimension d = getSize();
      int x = (d.width-backgroundPicture.getWidth(this))/2;
      int y = (d.height-backgroundPicture.getHeight(this))/2;
      g.drawImage(backgroundPicture, x, y, this); // Retaillé selon la taille de la fen?tre
    }
    //super.paint(g);

  }
}
