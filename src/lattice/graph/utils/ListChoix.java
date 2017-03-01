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

package lattice.graph.utils;import java.awt.List;import java.awt.event.ActionListener;import java.awt.event.ItemListener;import java.awt.event.MouseEvent;import java.awt.event.MouseListener;/**	* Implémente un Menu Choix avec passage automatique du Listener dans le constructeur*/public class ListChoix extends List implements ChoixComponent, MouseListener {	int choix;	InfoListener ibm;	String info;	public ListChoix(ActionListener listener, int choix) {		super();		this.choix = choix;		addActionListener(listener);		addMouseListener(this);		if(listener instanceof InfoListener) setListener((InfoListener) listener);	}	public ListChoix(int choix, ItemListener listener) {		super();		this.choix = choix;		addItemListener(listener);		addMouseListener(this);		if(listener instanceof InfoListener) setListener((InfoListener) listener);	}	public ListChoix(int rows, boolean mul, ActionListener listener, int choix) {		super(rows, mul);		this.choix = choix;		addActionListener(listener);		addMouseListener(this);		if(listener instanceof InfoListener) setListener((InfoListener) listener);	}	public ListChoix(int rows, boolean mul, int choix, ItemListener listener) {		super(rows, mul);		this.choix = choix;		addItemListener(listener);		addMouseListener(this);		if(listener instanceof InfoListener) setListener((InfoListener) listener);	}	public void setChoix(int choix) {		this.choix = choix;	}	public int getChoix() {		return choix;	}	public InfoListener getListener() {		return ibm;	}	public void setListener(InfoListener listener) {		ibm = listener;	}	public String getInfo() {		return info;	}	public void setInfo(String info) {		this.info = info;	}	public void afficherInfo() {		if((getInfo() != null) && (getListener() != null)) getListener().setInfo(getInfo());	}// implémente MouseListener	public void mouseEntered(MouseEvent e) {		afficherInfo();	}	public void mouseExited(MouseEvent e) {		if((getInfo() != null) && (getListener() != null)) getListener().removeInfo();	}	public void mousePressed(MouseEvent e) {	}	public void mouseReleased(MouseEvent e) {	}	public void mouseClicked(MouseEvent e) {		afficherInfo();	}}