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

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.event.MouseEvent;
import java.io.File;
import java.io.InputStream;
import java.net.URL;
import java.util.Vector;

import lattice.gui.graph.LatticeGraphViewer;
import lattice.gui.graph.LatticeNodeGraph;

/** An applet to put a Chemical/Atomic Lattice model into a page */
public class Lattice3D implements Runnable {
    XYZLatticeModel md;
    boolean painted = true;
    float xfac;
    int prevx, prevy;
    float xtheta, ytheta;
    float scalefudge = 1;
    Matrix3D amat = new Matrix3D(), tmat = new Matrix3D();
    String mdname = null;
    String message = null;
    boolean label = true;
    boolean box = false;
    boolean bonds = true;
    //Image backBuffer;
    Graphics backGC;
    Dimension backSize;
    String param;
    Color bgcolor = Color.white;
    Color bondcolor=Color.black;
    Color boxcolor=Color.darkGray;
    LatticeGraphViewer lgv;
    int decalX=0, decalY=0;

   // <param name=scale    value=0.8>
    //<param name=box      value=false>
    //<param name=bonds    value=true>
    //<param name=bgcolor  value="ffffff">
//<param name=bondcolor value="000000">

    public Lattice3D(LatticeGraphViewer lgv) {
      this.lgv = lgv;
      init();
    }

    public Dimension getSize() {
      return lgv.getSize();
    }

    /*private synchronized void newBackBuffer() {
        backBuffer = lgv.createImage(getSize().width, getSize().height);
        backGC = backBuffer.getGraphics();
        backSize = getSize();
    }*/

    public void init() {
      amat.yrot(20);
       amat.xrot(20);
       if (mdname == null)
           mdname = "model.obj";
       /*resize(getSize().width <= 20 ? 400 : getSize().width,
              getSize().height <= 20 ? 400 : getSize().height);*/
       //newBackBuffer();
    }

/*
    public void init() {
        mdname = getParameter("model");
        try {
            scalefudge = Float.valueOf(getParameter("scale")).floatValue();
        } catch(Exception e) {
        };
        try {
            label = Boolean.valueOf(getParameter("label")).booleanValue();
        } catch(Exception e) {
        };
        try {
            box = Boolean.valueOf(getParameter("box")).booleanValue();
        } catch(Exception e) {
        };
        try {
            bonds = Boolean.valueOf(getParameter("bonds")).booleanValue();
        } catch(Exception e) {
        };
        try {
            param = getParameter("bgcolor");
        } catch(Exception e) {
        };
        try {
           Integer i = Integer.valueOf(param, 16);
           bgcolor = new Color(i.intValue());
        } catch (NumberFormatException e) {
           bgcolor = Color.lightGray;
        }
        try {
            param = getParameter("bondcolor");
        } catch(Exception e) {
        };
        try {
           Integer i = Integer.valueOf(param, 16);
           bondcolor = new Color(i.intValue());
        } catch (NumberFormatException e) {
           bondcolor = Color.black;
        };
        try {
            param = getParameter("boxcolor");
        } catch(Exception e) {
        };
        try {
           Integer i = Integer.valueOf(param, 16);
           boxcolor = new Color(i.intValue());
        } catch (NumberFormatException e) {
           boxcolor = Color.red;
        };
        amat.yrot(20);
        amat.xrot(20);
        if (mdname == null)
            mdname = "model.obj";
        resize(getSize().width <= 20 ? 400 : getSize().width,
               getSize().height <= 20 ? 400 : getSize().height);
        newBackBuffer();
    }*/
    public void run() {
      buildLattice3D(lgv.getNiveau());
      //loadLattice();
    }

    public void buildLattice3D(Vector vNiveau) {
      XYZLatticeModel m = null;
      try {
        // m = new XYZLatModel (lgv, vNiveau, label, box, bonds, bgcolor, bondcolor, boxcolor);
        m = new XYZLatticeModel (lgv, vNiveau, label, box, bonds, Color.white, bondcolor, boxcolor);
      }
      catch(Exception e) {System.out.println("Unexpected error to build 3D lattice");}
      initXYZLatModel(m);
    }

    public void initXYZLatModel(XYZLatticeModel m) {
    LatticeNodeGraph.setApplet(lgv);
    md = m;
    m.findBB();
    initScale();
    /*float xw = m.xmax - m.xmin;
    float yw = m.ymax - m.ymin;
    float zw = m.zmax - m.zmin;
    if (yw > xw)
        xw = yw;
    if (zw > xw)
        xw = zw;
    float f1 = getSize().width / xw;
    float f2 = getSize().height / xw;
    xfac = 0.9f * (f1 < f2 ? f1 : f2) * scalefudge;*/
    lgv.repaint();
    }

    public void initScale() {
      float xw = md.xmax - md.xmin;
      float yw = md.ymax - md.ymin;
      float zw = md.zmax - md.zmin;
      if (yw > xw)
          xw = yw;
      if (zw > xw)
          xw = zw;
      float f1 = getSize().width / xw;
      float f2 = getSize().height / xw;
      xfac = 0.9f * (f1 < f2 ? f1 : f2) * scalefudge * ((float) lgv.getZoom()/9f);
      //System.out.println(lgv.getZoom());
    }

    public void loadLattice() {
        InputStream is = null;
        try {
            Thread.currentThread().setPriority(Thread.MIN_PRIORITY);
            //is = new URL(getDocumentBase(), mdname).openStream();
            URL url = new File("exempleLat3D/buckminsterfullerine.lat").toURL();
            System.out.println(url);
            is = url.openStream();
            XYZLatticeModel m = new XYZLatticeModel (is, label, box, bonds, bgcolor, bondcolor, boxcolor);
            initXYZLatModel(m);
        } catch(Exception e) {
            e.printStackTrace();
            md = null;
            message = e.toString();
        }
        try {
            if (is != null)
                is.close();
        } catch(Exception e) {
        }

    }
    public void start() {
        if (md == null && message == null)
            new Thread(this).start();
    }
    public void stop() {
    }
    public void mouseDown(MouseEvent e) {
      int x = e.getX();
      int y = e.getY();
        prevx = x;
        prevy = y;
    }
    public void mouseDragged(MouseEvent e) {
      int x = e.getX();
      int y = e.getY();
        tmat.unit();
        float xtheta = (prevy - y) * (360.0f / getSize().width);
        float ytheta = (x - prevx) * (360.0f / getSize().height);
        tmat.xrot(xtheta);
        tmat.yrot(ytheta);
        amat.mult(tmat);
        if (painted) {
            painted = false;
            lgv.repaint();
        }
        prevx = x;
        prevy = y;
    }

    public void rotation(float val) {
      //float xtheta = (prevy - y) * (360.0f / getSize().width);
      tmat.unit();
      //float ytheta = valRot * (360.0f / getSize().height);
      float ytheta = val;
      //tmat.xrot(xtheta);
      tmat.yrot(ytheta);
      amat.mult(tmat);
      if (painted) {
        painted = false;
        //lgv.repaint();
      }
    }

    public void update(Graphics g) {
        //if (backBuffer == null)
        g.clearRect(0, 0, getSize().width, getSize().height);
        paint(g);
    }

    public void paint(Graphics g) {
        if (md != null) {
            md.mat.unit();

            // CoordonnŽes du centre de rotation
            md.mat.translate(-(md.xmin + md.xmax) / 2,
                             -(md.ymin + md.ymax) / 2,
                             -(md.zmin + md.zmax) / 2);
            md.mat.mult(amat);
            // md.mat.scale(xfac, -xfac, 8 * xfac / size().width);
            //md.mat.scale(xfac, -xfac, 16 * xfac / getSize().width);
            initScale();
            md.mat.scale(xfac, -xfac, 16 * xfac / getSize().width);
            md.mat.translate(getSize().width / 2, getSize().height / 2, 8);
            md.transformed = false;
            //System.out.println("X:"+lgv.getX()+"Y:"+lgv.getY());
            /*if (backBuffer != null) {
                if (!backSize.equals(getSize()))
                    newBackBuffer();
                //setBackground(bgcolor);
                backGC.setColor(bgcolor);
                backGC.fillRect(0,0,getSize().width,getSize().height);
                md.paint(backGC);
                g.drawImage(backBuffer, 0, 0, lgv);
            }
            else*/
             g.setColor(Color.white);
             g.fillRect(0,0,getSize().width,getSize().height);
             //g.clearRect(0,0,getSize().width,getSize().height);
             md.paint(g);
             setPainted();
        } else if (message != null) {
            g.drawString("Error in model:", 3, 20);
            g.drawString(message, 10, 40);
        }
    }
    private synchronized void setPainted() {
        painted = true;
        notifyAll();
    }

    private synchronized void waitPainted()
    {
       while (!painted)
       {
          try
          {
             wait();
          }
          catch (InterruptedException e) {}
       }
       painted = false;
    }
}   // end class LatticeViewer