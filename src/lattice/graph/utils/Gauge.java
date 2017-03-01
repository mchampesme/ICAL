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

package lattice.graph.utils;/* * @(#)Gauge.java	1.2 97/01/14 Jeff Dinkins * * Copyright (c) 1995-1997 Sun Microsystems, Inc. All Rights Reserved. * */import java.awt.Color;import java.awt.Component;import java.awt.Dimension;import java.awt.Graphics;/* * Gauge - a class that implements a lightweight component * that can be used, for example, as a performance meter. * * Lightweight components can have "transparent" areas, meaning that * you can see the background of the container behind these areas. * */public class Gauge extends Component {  // the current and total amounts that the gauge reperesents  int current = 0;  int total = 100;  // The preferred size of the gauge  int Height = 18;   // looks good  int Width  = 250;  // arbitrary   protected Rectangle3D r3D;   protected Color gaugeColor;  /**   * Constructs a Gauge   */  public Gauge() {      this(Color.blue);  }  /**   * Constructs a that will be drawn uses the   * specified color.   *   * @gaugeColor the color of this Gauge   */  public Gauge(Color gaugeColor) {      setBackground(Color.white);      this.gaugeColor = gaugeColor;  }  public void paint(Graphics g) {  		r3D = new Rectangle3D(Color.lightGray, 0, 0, getSize().width, getSize().height);  		r3D.setDrawingMode(Rectangle3D.IN);  	 	//g.fillRect(0, 0, getSize().width, getSize().height);  	 	//g.setColor(Color.lightGray);      	//g.fillRect(0, 0, getSize().width, getSize().height);      	r3D.paint(g);      	int barWidth = (int) (((float)current/(float)total) * getSize().width);      	r3D.setDrawingMode(Rectangle3D.OUT);      	r3D.setColor(gaugeColor);      	r3D.setWidth(barWidth-3);      	r3D.setHeight(getSize().height-4);      	r3D.setX(1);      	r3D.setY(2);      	r3D.setDrawingMode(Rectangle3D.OUT);      	r3D.paint(g);      	//g.setColor(Color.blue);     	//g.fill3DRect(0, 0, barWidth, getSize().height-2, true);  }  public void setCurrentAmount(int Amount) {      current = Amount;      // make sure we don't go over total      if(current > 100)       current = 100;      repaint();  }	public void setColor(Color c) {		this.gaugeColor = c;	}  public int getCurrentAmount() {      return current;  }  public int getTotalAmount() {      return total;  }  public Dimension getPreferredSize() {      return new Dimension(Width, Height);  }  public Dimension getMinimumSize() {      return new Dimension(Width, Height);  }}