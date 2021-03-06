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

package lattice.graph.utils;

import java.awt.TextField;
import java.awt.event.ActionListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;

public class TextFieldChoix extends TextField implements ChoixComponent, MouseListener {

	protected int choix;
	protected String info;
	protected InfoListener ibm;

	public TextFieldChoix(String label, int largeur, ActionListener listener, int choix) {
		super(label, largeur);
		this.choix = choix;
		addActionListener(listener);
		addMouseListener(this);
		if(listener instanceof InfoListener) ibm = (InfoListener) listener;
	}

/**
	* R�cup�rer le recepteur des images
*/
	public InfoListener getListener() {
		return ibm;
	}

/**
	* affecter le recepteur des images
*/
	public void setInfoListener(InfoListener il) {
		this.ibm = il;
	}

	public int getChoix() {
		return choix;
	}

	public void setChoix(int i) {
		choix = i;
	}


	public String getInfo() {
		return info;
	}

	public void setInfo(String s) {
		this.info = s;
	}

	protected void afficherInfo() {
		if((getInfo() != null) && (getListener() != null)) getListener().setInfo(getInfo());
	}

	// impl�mente MouseListener
	public void mouseEntered(MouseEvent e) {
		afficherInfo();
	}
	public void mouseExited(MouseEvent e) {
		if((getInfo() != null) && (getListener() != null)) getListener().removeInfo();
	}
	public void mousePressed(MouseEvent e) {

	}
	public void mouseReleased(MouseEvent e) {

	}
	public void mouseClicked(MouseEvent e) {
		afficherInfo();
	}
}