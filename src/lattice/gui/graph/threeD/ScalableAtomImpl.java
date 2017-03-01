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

package lattice.gui.graph.threeD;

import java.awt.Component;
import java.awt.Graphics;
import java.awt.Image;
import java.awt.image.IndexColorModel;
import java.awt.image.MemoryImageSource;

/**
 * <p>Title: Galicia</p>
 * <p>Description: Galois Lattice Interactive Constructor</p>
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: University of Montreal</p>
 * @author David Grosser
 * @version 1.0
 */

class ScalableAtomImpl implements ScalableAtom {
    private static Component applet;
    private static byte[] data;
    private final static int R = 40;
    private final static int hx = 15;
    private final static int hy = 15;
    private final static int bgGrey = 192;
    private static int maxr;

    private int Rl;
    private int Gl;
    private int Bl;
    private double Sf;

    private Image balls[];

    static {
        data = new byte[R * 2 * R * 2];
        int mr = 0;
        for (int Y = 2 * R; --Y >= 0;) {
            int x0 = (int) (Math.sqrt(R * R - (Y - R) * (Y - R)) + 0.5);
            int p = Y * (R * 2) + R - x0;
            for (int X = -x0; X < x0; X++) {
                int x = X + hx;
                int y = Y - R + hy;
                int r = (int) (Math.sqrt(x * x + y * y) + 0.5);
                if (r > mr)
                    mr = r;
                data[p++] = r <= 0 ? (byte) 1 : (byte) r;
            }
        }
        maxr = mr;
    }
    static void setApplet(Component app) {
        applet = app;
    }
    ScalableAtomImpl(int Rl, int Gl, int Bl, double Sf) {
        this.Rl = Rl;
        this.Gl = Gl;
        this.Bl = Bl;
        this.Sf = Sf;
    }
    public boolean Exist() {
        if (Sf==0.0)
            return false;
        else
            return true;
    }
    public final int blend(int fg, int bg, float fgfactor) {
        return (int) (bg + (fg - bg) * fgfactor);
    }
    public void Setup(int nBalls) {
        balls = new Image[nBalls];
        byte red[] = new byte[256];
        red[0] = (byte) bgGrey;
        byte green[] = new byte[256];
        green[0] = (byte) bgGrey;
        byte blue[] = new byte[256];
        blue[0] = (byte) bgGrey;
        for (int r = 0; r < nBalls; r++) {
            float b = (float) (r+1) / nBalls;
            for (int i = maxr; i >= 1; --i) {
                float d = (float) i / maxr;
                red[i] = (byte) blend(blend(Rl, 255, d), bgGrey, b);
                green[i] = (byte) blend(blend(Gl, 255, d), bgGrey, b);
                blue[i] = (byte) blend(blend(Bl, 255, d), bgGrey, b);
            }
            IndexColorModel model = new IndexColorModel(8, maxr + 1,
                                                        red, green, blue, 0);
            balls[r] = applet.createImage(
                new MemoryImageSource(R*2, R*2, model, data, 0, R*2));
        }
    }
    public void paint(Graphics gc, int x, int y, int r) {
        Image ba[] = balls;
        if (ba == null) {
            Setup((int)(16*Sf));
            ba = balls;
        }
        r=(int)(r*Sf);
        Image i = ba[r];
        int size = 10 + r;
        gc.drawImage(i, x - (size >> 1), y - (size >> 1), size, size, applet);
    }
}
