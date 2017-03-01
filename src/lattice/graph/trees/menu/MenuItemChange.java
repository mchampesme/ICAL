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

package lattice.graph.trees.menu;

import java.awt.MenuItem;

public class MenuItemChange extends MenuItem {

	String label1, label2;
	boolean state = true;

	public MenuItemChange(String label1, String label2) {
		super(label1);
		this.label1 = label1;
		this.label2 = label2;
	}

	public void changeLabel() {
		state = ! state;
		if(state) setLabel(label1);
		else setLabel(label2);
	}

	public boolean getState() {
		return state;
	}

	public void setState(boolean b) {
		this.state = b ;
		if(state) setLabel(label1);
		else setLabel(label2);
	}

}