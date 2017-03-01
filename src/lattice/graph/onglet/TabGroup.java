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

package lattice.graph.onglet;import java.awt.CardLayout;import java.awt.Color;import java.awt.Component;import java.awt.FlowLayout;import java.awt.FontMetrics;import java.awt.Graphics;import java.awt.Panel;/**	*      Stephane Calderoni and Jean-Christophe Soulie	* MAS2 Research Group - IREMIA - Universite de la Reunion	*        Copyright (c) 1998 - All Rights Reserved*/public class TabGroup extends Panel {  	public static int margin = 2;  	private Panel target;  	private int   selected;	private String label;	private Color bgColor = Color.white;  	public TabGroup (String [] labels, Panel p) {    	super(new FlowLayout(FlowLayout.LEFT, 0, 0));    	//super (new GridBagLayout ());      	setBackground (Color.white);      	target = p;      	for (int i=0; i<labels.length; i++)      		add (new Tab (labels [i],this,i));      	label = new String("");      	selected = 0;      	getTab (selected).select();    }  	private Tab getTab (int n) {    	return (Tab) (getComponent (n));    }  	void select(int newSelected) {    	getTab (selected).unselect();    	selected = newSelected;    	getTab (selected).select();     	((CardLayout) (target.getLayout ())).show(target, getTab (selected).getLabel());    }	public void paint(Graphics g) {		paintBackground (g);		super.paint(g);	}/**	* dessin du background*/	private void paintBackground(Graphics g) {		int w = getSize().width;		int h = getSize().height;		//g.clearRect(0, 0, w, h);		FontMetrics fontMet = getFontMetrics (getFont ());		int lh = fontMet.getHeight ();		int th = 2*margin + lh;		g.setColor (CardPanel.backgroundColor.darker ());		g.fillRect (1,1,w,th);		g.setColor (Color.black);		g.drawLine (w-1,0,w-1,th);		g.drawLine (0,th,w-1,th);		g.drawLine (0,th+1,w-1,th+1);		g.setColor (CardPanel.backgroundColor);		g.drawLine (0,th+2,w-1,th+2);		g.setColor (CardPanel.backgroundColor.brighter ());		g.drawLine (0,th+3,w-1,th+3);		g.drawLine (0,th+4,w-1,th+4);		int xEnd = 0;// La largeur de tous les composants		/*		Component [] components = getComponents ();		if(CardPanel.align == CardPanel.CENTER) {		for (int i=0; i<components.length; i++) xEnd += components[i].getPreferredSize().width;		xEnd = ((getSize ().width - xEnd) / 2) + xEnd;		}*/		// if(CardPanel.align == LEFT) xEnd = ((getSize ().width - xEnd) / 2) + xEnd;		g.setColor (getBackground());		g.drawLine (xEnd,0,xEnd,th-1);		// g.setColor (Color.lightGray);		if(CardPanel.paintDownBar) paintDownBar(g, w, h);		afficheLabel(g);	}    public void setBgColor(Color c) {    	bgColor = c;    	setBackground(c);    }    public Color getBgColor() {		return bgColor;    }/**	* affichage du label*/	public void afficheLabel(Graphics g) {		try {	      g.setColor(bgColor);	      FontMetrics fontMet = getFontMetrics (getFont ());		  int lh = fontMet.getHeight();		  g.drawString(label, comLargeur()+4, (lh + margin) - fontMet.getMaxDescent ());	  	} catch(NullPointerException e) {}	}/**	* effacement du label*/	public void effacerLabel(Graphics g) {		try {                        label = "";			paintBackground(g);                        //g.setColor(CardPanel.backgroundColor.darker ());			//FontMetrics fontMet = getFontMetrics (getFont ());			//int lh = fontMet.getHeight();			//g.drawString(label, comLargeur()+4, (lh + margin) - fontMet.getMaxDescent ());                } catch(NullPointerException e) {}	}/**	* affichage de l'info*/	public void setInfo(String s) {		effacerLabel(getGraphics());		label = s;		afficheLabel(getGraphics());	}/**	* affichage de l'info*/	/*public void removeInfo() {		effacerLabel(getGraphics());		//label = s;		//afficheLabel(getGraphics());	}*//**	* Calcul de la largeur des composants*/	public int comLargeur() {		int l = 0;		Component [] components = getComponents ();		for (int i=0; i<components.length; i++) {			l += components[i].getPreferredSize().width;		}		return l;	}/**	* paintDownBar*/    private void paintDownBar(Graphics g, int w, int h) {      g.setColor (CardPanel.backgroundColor.brighter ());      g.drawLine (0,h-4,w-1,h-4);      g.drawLine (0,h-3,w-1,h-3);      g.setColor (Color.gray);      g.drawLine (0,h-2,w-1,h-2);      g.setColor (Color.black);      g.drawLine (0,h-1,w-1,h-1);    }}