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

package lattice.graph.onglet;/*** Ce composant a été prété par :**           Stéphane Calderoni** IREMIA - Universite de la Reunion*/import java.awt.BorderLayout;import java.awt.CardLayout;import java.awt.Color;import java.awt.Component;import java.awt.Panel;public class CardPanel extends Panel {	TabGroup tabs;// Constantes	public static final int LEFT = 0;	public static final int CENTER = 1;	public static final int RIGHT = 2;// variables statiques	public static int align = CENTER;	//public static Color backgroundColor = new Color(170, 221, 239);	public static Color backgroundColor = new Color(160, 160, 180);	public static boolean paintDownBar = false; 	 public CardPanel (String [] labels, Component [] components) {      	super (new BorderLayout ());      	if (labels.length == components.length) {	 		Panel cards = new Panel (new CardLayout ());	  		for (int i=0; i<labels.length; i++) cards.add (components [i],labels [i]);	  		tabs = new TabGroup (labels,cards);	  		add ("North", tabs);	 		add ("Center", cards);		}    }    public void setInfo(String s) {    	tabs.setInfo(s);    }    public void setBgColor(Color c) {    	tabs.setBgColor(c);    }}