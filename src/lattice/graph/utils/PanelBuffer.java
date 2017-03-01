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

package lattice.graph.utils;/**	* IKBS - Editeur des cas	* DŽfinition de Panel3D, sous classe de Panel	* Version 1.0	* David Grosser - 17 FŽvrier 1997*/import java.awt.Dimension;import java.awt.Graphics;import java.awt.Image;public class PanelBuffer extends IkbsPanel {// Les variables d'instance pour la gestion du double buffering	protected Image offscreen;					// L'image du double buffer   	protected Dimension offscreensize;			// Dimension du double buffer   	protected Graphics offgraphics;				// Le contexte graphique	protected boolean doubleBuffer = true;	public Image offscreen() {		return offscreen;	}	public boolean getDoubleBuffer() {		return doubleBuffer;	}	public void setDoubleBuffer(boolean b) {		this.doubleBuffer = b;	}	protected void initOffGraphics(Graphics g, Dimension d) {		if (	(offscreen == null) ||				(d.width != offscreensize.width) ||				(d.height != offscreensize.height))		{	    	offscreen = createImage(d.width, d.height);	    	offscreensize = d;	    	offgraphics = offscreen.getGraphics();	    	offgraphics.setFont(getFont());		}	}    public synchronized void update(Graphics g) {    	if(doubleBuffer) {	    	Dimension d = getSize();			drawZoom(g, d);			initOffGraphics(g, d);			if(g == null) System.out.println("g est null");			//if((offscreen != null)&&(offgraphics!=null)) {				paint(offgraphics);				g.drawImage(offscreen, 0, 0, this);			//}			//else paint(g);		}		else super.update(g);    }	public void drawZoom(Graphics g, Dimension d) {}	public void dispose() {		if (offscreen != null) offscreen.flush();		if (offgraphics != null) offgraphics.dispose();		System.gc();	}	public void setBounds(int x, int y, int w, int h) {		offgraphics = null;		super.setBounds(x, y, w, h);	}}