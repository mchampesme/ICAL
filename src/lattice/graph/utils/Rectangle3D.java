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

import java.awt.Color;
import java.awt.Graphics;

/**
 * Draw a 3D rectangle on a Graphics area. The 3D effect
 * can be either in, out, border only in or border only out.
 *
 * @author Shaun Terry
 */

public class Rectangle3D {

	public final static int IN = 0;
	public final static int OUT = 1;
	public final static int BORDER_IN = 2;
	public final static int BORDER_OUT = 3;

	int mode = IN;

	Color color;

	int w, h, x, y;

	public Rectangle3D(Color c, int X, int Y, int width, int height) {
		x = X;
		y = Y;
		w = width;
		h = height;
		color = c;
	}

	public void setDrawingMode(int m) {
		mode = m;
	}

	public void setColor(Color c) {
		color = c;;
	}

	static public int borderWidthOfMode(int m) {
		return 2;	// They're all 2 right now
	}

	public void setWidth(int w) {
		this.w = w;
	}

	public void setHeight(int h) {
		this.h = h;
	}

	public void setX(int x) {
		this.x = x;
	}

	public void setY(int y) {
		this.y = y;
	}


    public synchronized void paint(Graphics g) {
		Color c = color;
		Color darker = c.darker();
		Color brighter = c.brighter();

		Color c1, c2, c3, c4, c5;

		if (mode == IN) {
			c1 = darker;
			c2 = brighter;
			c3 = c;
			c4 = Color.black;
			c5 = darker;
		}
		else if (mode == OUT) {
			c3 = darker;
			c2 = darker;
			c4 = c;
			c1 = brighter;
			c5 = c;
		}
		else if (mode == BORDER_OUT) {
			c4 = darker;
			c2 = darker;
			c1 = brighter;
			c3 = brighter;
			c5 = c;
		}
		else /* if (mode == BORDER_IN) */ {
			c1 = darker;
			c2 = brighter;
			c3 = c1;
			c4 = brighter;
			c5 = c;
		}

		// Upper left, outer
		g.setColor(c1);
		g.drawLine(x, y, x+w-1, y);
		g.drawLine(x, y, x, y+h-1);

		// Upper left, inner
		g.setColor(c4);
		g.drawLine(x+1, y+1, x+w-2, y+1);
		g.drawLine(x+1, y+1, x+1, y+h-2);

		// Lower right, outer
		g.setColor(c2);
		g.drawLine(x, y+h-1, x+w-1, y+h-1);
		g.drawLine(x+w-1, y, x+w-1, y+h-1);

		// Lower right, inner
		g.setColor(c3);
		g.drawLine(x+1, y+h-2, x+w-2, y+h-2);
		g.drawLine(x+w-2, y+1, x+w-2, y+h-2);

		g.setColor(c5);
		g.fillRect(x+2, y+2, w-4, h-4);
	}
}

