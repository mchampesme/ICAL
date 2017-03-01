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

package lattice.graph.zoom;import java.awt.Color;import java.awt.Dimension;import java.awt.Graphics;import java.awt.Rectangle;/**	* tools - ZoomInterface	* Interface des classes qui souhaitent pouvoir ?tre zoomée	* @author David Grosser	* @date 19 Avril 2000*/public interface ZoomInterface {	public abstract Color getBackground();	public abstract Rectangle dimension();	public abstract int getX();	public abstract int getY();	public abstract void setX(int x);	public abstract void setY(int y);	public abstract void setPosX(int x);	public abstract void setPosY(int y);	public abstract int getPosX();	public abstract int getPosY();	public abstract Dimension getSize();        public abstract void paintOffscreen(Graphics g, Rectangle rect);	public abstract void paintOffscreen(Graphics g, int x, int y, float factor);	public abstract void dragMode();	public abstract void recentre(int x, int y);	public abstract void deplacer(int x, int y);	public abstract boolean mouseUp(int x, int y);        public abstract void setZoomViewer(ZoomViewer z);}