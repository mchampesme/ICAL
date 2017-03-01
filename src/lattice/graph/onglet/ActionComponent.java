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

package lattice.graph.onglet;import java.awt.AWTEvent;import java.awt.AWTEventMulticaster;import java.awt.Image;import java.awt.Panel;import java.awt.event.ActionListener;import java.awt.event.MouseEvent;public class ActionComponent extends Panel {// Constantes  protected static int margin = 5;// Variables d'instance  protected boolean        state = false;  protected ActionListener actionListener;  private   Image          offscreen;// Constructeur	public ActionComponent () {		enableEvents (AWTEvent.MOUSE_EVENT_MASK);    }	public void select () {		state = true;		repaint ();	}	public void unselect () {      state = false;      repaint ();	}  // ----------------------  // Affichage du composant  // ----------------------  /*public void update (Graphics g)    {      int w = getSize ().width;      int h = getSize ().height;      if (offscreen == null)      	offscreen = createImage (w,h);      else      	{	  int iw = offscreen.getWidth (this);	  int ih = offscreen.getHeight (this);	  if ((w != iw) || (h != ih))	    offscreen = createImage (w,h);      	}      Graphics offg = offscreen.getGraphics ();      offg.clearRect (0,0,w,h);      paint (offg);      g.drawImage (offscreen,0,0,this);    }*/  // ---------------------  // Gestion des Listeners  // ---------------------	public void addActionListener (ActionListener listener) {		actionListener = AWTEventMulticaster.add (actionListener,listener);		enableEvents (AWTEvent.MOUSE_EVENT_MASK);    }	public void removeActionListener (ActionListener listener) {		actionListener = AWTEventMulticaster.remove (actionListener,listener);	}/**	* Gestion des evenements souris*/	public void processMouseEvent (MouseEvent e) {		switch (e.getID()) {			case MouseEvent.MOUSE_PRESSED : select (); break;     	}		super.processMouseEvent (e);	}}