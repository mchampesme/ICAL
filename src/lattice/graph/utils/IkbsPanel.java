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

package lattice.graph.utils;import java.awt.Component;import java.awt.Container;import java.awt.Dimension;import java.awt.Frame;import java.awt.GridBagConstraints;import java.awt.GridBagLayout;import java.awt.Insets;import javax.swing.JPanel;public class IkbsPanel extends JPanel implements GetFrame {	public GridBagConstraints c;	public void initGridBagConstraint() {		c = new GridBagConstraints();		c.ipadx = 0;		c.ipady = 0;		c.gridheight=1;		c.fill=GridBagConstraints.BOTH;		c.weightx=0.0; c.weighty=0.0;		c.anchor=GridBagConstraints.CENTER;		c.insets=new Insets(2, 2, 2, 2);	}	public Dimension adaptedSize() {		return new Dimension(100, 100);	}	// Pour positionner correctement les composants dans le container	public void xyPosition(Container conteneur, Component element, int x, int y, int gridwidth)	{		if (c==null) initGridBagConstraint();		c.gridx=x; c.gridy=y;		c.gridwidth = gridwidth;		((GridBagLayout) conteneur.getLayout()).setConstraints(element, c);		conteneur.add(element);	}	// Pour positionner correctement les composants dans le container (avec weightx)	public void xyPosition(Container conteneur, Component element, int x, int y, int gridwidth, double weightx)	{		if (c==null) initGridBagConstraint();		c.gridx=x; c.gridy=y;		c.gridwidth = gridwidth;		c.weightx=weightx;		((GridBagLayout) conteneur.getLayout()).setConstraints(element, c);		conteneur.add(element);		//c.weightx=0.0;	}	public Frame getFrame() {return ((GetFrame) getParent()).getFrame();}}