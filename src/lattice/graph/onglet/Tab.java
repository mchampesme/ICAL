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

package lattice.graph.onglet;/***                       G E A M A S****      Stephane Calderoni and Jean-Christophe Soulie** MAS2 Research Group - IREMIA - Universite de la Reunion**        Copyright (c) 1998 - All Rights Reserved** Modifi� par David Grosser le 20 janvier 2000*/import java.awt.Color;import java.awt.Dimension;import java.awt.FontMetrics;import java.awt.Graphics;import java.awt.event.MouseEvent;public class Tab extends ActionComponent{  // ----------  // Proprietes  // ----------  private String   label;  private TabGroup group;  private int      rank;  // ------------  // Constructeur  // ------------    public Tab(String s, TabGroup g, int n) {	  	margin = TabGroup.margin;	    label = s;	    group = g;	    rank = n;	    setForeground (Color.green);	}  // ----------------------  // Etiquette du composant  // ----------------------  String getLabel() {      return label;  }  // -------------------  // Taille du composant  // -------------------  public Dimension getPreferredSize() {      FontMetrics fontMet = getFontMetrics (getFont ());      int width = fontMet.stringWidth (label);      int height = fontMet.getHeight ();      //return new Dimension (margin*2+width+2*height, 3*margin+2*height+10);      return new Dimension (margin*2+width+2*height, 3*margin+2*height+3);      //return new Dimension(200, 200);    }  	public void paint (Graphics g) {    	paintBackground (g);    	paintLabel (g);    }  	private void paintBackground (Graphics g) {    	  int w = getSize ().width;      	  int h = getSize ().height;	      FontMetrics fontMet = getFontMetrics (getFont ());	      int         lw      = fontMet.stringWidth (label);	      int         lh      = fontMet.getHeight ();	      int         th      = 2*margin + lh;	      g.setColor (CardPanel.backgroundColor.darker ());	      g.fillRect (1,1,w,th);	      g.setColor (Color.black);	      g.drawLine (w-1,0,w-1,th);	      g.drawLine (0,th,w-1,th);	      g.drawLine (0,th+1,w-1,th+1);	      g.setColor (CardPanel.backgroundColor);	      g.drawLine (0,th+2,w-1,th+2);	      g.setColor (CardPanel.backgroundColor.brighter ());	      g.drawLine (0,th+3,w-1,th+3);	      g.drawLine (0,th+4,w-1,th+4);		  if(CardPanel.paintDownBar) paintDownBar(g, w, h);	      if (state) {		  int [] x = {0,margin+lh-1,margin+lh+lw,w-1};		  int [] y = {th,th+margin+lh-1,th+margin+lh-1,th};		  g.setColor (CardPanel.backgroundColor.darker ());		  g.fillPolygon (x,y,4);		  g.setColor (group.getBgColor());		  g.drawLine (x[0],y[0],x[1],y[1]);		  g.setColor (Color.black);		  g.drawLine (x[0],y[0]+1,x[1],y[1]+1);		  g.drawLine (x[1],y[1],x[2],y[2]);		  g.drawLine (x[1],y[1]+1,x[2],y[2]+1);		  g.drawLine (x[2],y[2],x[3],y[3]);		  g.drawLine (x[2],y[2]+1,x[3],y[3]+1);		  g.setColor (CardPanel.backgroundColor);		  g.drawLine (x[1]+5,y[1]+2,x[2],y[2]+2);		  g.drawLine (x[2],y[2]+2,x[3],y[3]+2);		  g.setColor (CardPanel.backgroundColor.brighter ());		  g.drawLine (x[1]+6,y[1]+3,x[2],y[2]+3);		  g.drawLine (x[2],y[2]+3,x[3],y[3]+3);		  g.drawLine (x[1]+7,y[1]+4,x[2],y[2]+4);		  g.drawLine (x[2],y[2]+4,x[3],y[3]+4);		}    }  protected void paintDownBar(Graphics g, int w, int h) {      g.setColor (CardPanel.backgroundColor.brighter ());      g.drawLine (0,h-4,w-1,h-4);      g.drawLine (0,h-3,w-1,h-3);      g.setColor (Color.gray);      g.drawLine (0,h-2,w-1,h-2);      g.setColor (Color.black);      g.drawLine (0,h-1,w-1,h-1);  }  protected void paintLabel (Graphics g)    {      FontMetrics fontMet = getFontMetrics (getFont());      int         lh      = fontMet.getHeight();      int         trans   = state ? lh+margin-2 : 0;      int         width   = getSize ().width;      //g.setColor (state ? getForeground() : getBackground());      g.setColor (state ? getForeground() : group.getBgColor());      g.drawString(label, (width - fontMet.stringWidth (label))/2, trans + (lh+margin) - fontMet.getMaxDescent ());    }  // -----------------------------  // Gestion des evenements souris  // ----------------------------- 	public void processMouseEvent (MouseEvent e) {		switch (e.getID()) {			case MouseEvent.MOUSE_PRESSED : group.select(rank); break;    		default: break;    	}		super.processMouseEvent (e);	}}