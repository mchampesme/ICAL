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
import java.awt.Font;
import java.awt.FontMetrics;
import java.awt.Graphics;
import java.io.BufferedInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.StreamTokenizer;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Vector;

import lattice.gui.graph.LatticeGraphViewer;
import lattice.gui.graph.LatticeNodeGraph;

/**
 * <p>Title: Galicia</p>
 * <p>Description: Galois Lattice Interactive Constructor</p>
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: University of Montreal</p>
 * @author David Grosser
 * @version 1.0
 */

/** The representation of a Chemical .xyz or Atomic Lattice (.lat) model */
class XYZLatticeModel {
  float vert[];
  Vector vVert = new Vector();
  ScalableAtom atoms[];
  int tvert[];
  int ZsortMap[];
  int nvert, maxvert;
  int bond[][] = new int[300][2];
  int nbond = -1;
  boolean box;
  boolean label;
  boolean bonds;
  int br, bg, bb;	// RGB of bonds
  int gr, gg, gb;	// RGB of background
  int xr, xg, xb;	// RGB of box
  int decalX = 0, decalY=0;
  int nbAtom = 1;

  static Hashtable atomTable, atomNumber;
  static ScalableAtom defaultAtom;

  boolean transformed;
  Matrix3D mat;

  float xmin, xmax, ymin, ymax, zmin, zmax;

  LatticeGraphViewer lgv;

  XYZLatticeModel () {
    mat = new Matrix3D();
    mat.xrot(20);
    //mat.xrot(0);
    mat.yrot(30);
    //mat.yrot(0);
  }

  XYZLatticeModel (LatticeGraphViewer lgv, Vector niveau, boolean labl, boolean bx, boolean bnds, Color bgcolor, Color bndcolor, Color bxcolor) throws Exception{
    this();
    this.lgv = lgv;
    this.label=labl;
    this.box=bx;
    this.bonds=bnds;
    this.br=bndcolor.getRed();
    this.bg=bndcolor.getGreen();
    this.bb=bndcolor.getBlue();
    this.gr=bgcolor.getRed();
    this.gg=bgcolor.getGreen();
    this.gb=bgcolor.getBlue();
    this.xr=bxcolor.getRed();
    this.xg=bxcolor.getGreen();
    this.xb=bxcolor.getBlue();
    atomTable = new Hashtable();
    atomNumber = new Hashtable();

    addAllVert(niveau);
    addAllRelation(niveau);
    //buildModel(niveau);
  }

/*  public void buildModel(Vector niveau) {
    int nbNiveau = niveau.size();
    double beta = Math.PI/(double) (nbNiveau-1);
    for(int i=0; i<nbNiveau; i++) { // Build vertex
      Vector vNiv = (Vector) niveau.elementAt(i);
      System.out.println("Level n "+i);
      if((i==0)||(i==nbNiveau-1)) buildNiveauModel(vNiv, Math.sin(i*beta), true, 0.0);
      else buildNiveauModel(vNiv, Math.sin(i*beta), false);
      addVert(vNiv);
    }

    for(int i=0; i<nbNiveau; i++) {// build links
      Vector vNiv = (Vector) niveau.elementAt(i);
      buildNiveauRelation(vNiv);
    }
  }

  public void buildNiveauModel(Vector niveau, double larg, boolean b) {
    boolean stop = false;
    double gamma = 0.0;
    buildNiveauModel(niveau, larg, b, gamma);
    double tension = calcTension(niveau);
    double tension2;
    double dGamma = Math.PI/12;
    int i=0;
    boolean right = false;
    while((! stop)&&(i<100)) {
  //while(! stop) {
      i += 1;
      gamma += dGamma;
      buildNiveauModel(niveau, larg, b, gamma);
      tension2 = calcTension(niveau);
      System.out.println("tension = "+tension+" tension2 = "+tension2);
      if(tension <= tension2) {
        if(dGamma < 0.0) {
          gamma -= dGamma;
          buildNiveauModel(niveau, larg, b, gamma);
          stop = true;
        }
        else {
          dGamma = -dGamma;
          gamma += dGamma;
          buildNiveauModel(niveau, larg, b, gamma);
          if(right)
            stop = true;
          tension = calcTension(niveau);
  //gamma += dGamma;
  //buildNiveauModel(niveau, larg, b, gamma);
  //stop = true;
        }
      }
      else {
        right = true;
        tension = tension2;
      }
    }

  }*/
  /**
   * For each level
   */
  /*public void buildNiveauModel(Vector niveau, double larg, boolean b, double gamma) {
    LatticeNodeGraph unNoeud;
    double x, z;
    int nbNode = niveau.size();
    double alpha = 2*Math.PI/nbNode;
    for(int i=0; i<nbNode; i++) {
      unNoeud = (LatticeNodeGraph) niveau.elementAt(i);
      //y = (double) -unNoeud.y();
      x = larg * 200.0 * Math.cos((i*alpha)+gamma);
      z = larg * 200.0 * Math.sin((i*alpha)+gamma);
      if(b) unNoeud.init3D(255, 0, 0, 1.5);
      else unNoeud.init3D(140, 140, 140, 1.4);
      //if(b) atomTable.put(unNoeud.getLabel().toLowerCase(), new ScaleableAtom(255, 0, 0, 1.5));
      //else
      unNoeud.setX(x);
      unNoeud.setZ(z);
      //addVert(unNoeud);
    }
  }

private double calcTension(Vector niveau) {
  LatticeNodeGraph unNoeud;
  double sommeTension = 0.0;
  for(int i=0; i<niveau.size(); i++) {
    unNoeud = (LatticeNodeGraph) niveau.elementAt(i);
    unNoeud.tensionX = Double.MIN_VALUE;
    unNoeud.tensionZ = Double.MIN_VALUE;
    sommeTension += Math.abs(unNoeud.tensionX(false));
    sommeTension += Math.abs(unNoeud.tensionZ(false));
  }
  return sommeTension;
}*/

  private void addAllVert(Vector niveau) {
    for(int i=0; i<niveau.size(); i++)
      addVert((Vector) niveau.elementAt(i));
  }

  private void addVert(Vector vniveau) {
    for(int i=0; i<vniveau.size(); i++)
      addVert((LatticeNodeGraph) vniveau.elementAt(i));
  }

  private void addVert(LatticeNodeGraph unNoeud) {
    atomTable.put(unNoeud.getLabel().toLowerCase(), unNoeud);
    addVert(unNoeud.getLabel(), (float) unNoeud.xd(), (float) -unNoeud.yd(), (float) unNoeud.zd());
    atomNumber.put(unNoeud.getLabel().toLowerCase(), new Integer(nvert));
    vVert.add(unNoeud);
  }

  private void addAllRelation(Vector niveau) {
    for(int i=0; i<niveau.size(); i++)
      buildNiveauRelation((Vector) niveau.elementAt(i));
  }
  /**
   * For each level, constructiong relations between nodes
   */
  public void buildNiveauRelation(Vector niveau) {
    LatticeNodeGraph unNoeud, unfils;
    int nbNode = niveau.size();
    for(int i=0; i<nbNode; i++) {
      unNoeud = (LatticeNodeGraph) niveau.elementAt(i);
      for(int j=0; j<unNoeud.nbRelationDepart(); j++) {
        unfils = (LatticeNodeGraph) unNoeud.relationDepart(j).extremite();
        int number = ((Integer) atomNumber.get(unNoeud.getLabel().toLowerCase())).intValue();
        int number2 = ((Integer) atomNumber.get(unfils.getLabel().toLowerCase())).intValue();

        //System.out.println(number);
        nbond++;
        bond[nbond][0]=number2;
        bond[nbond][1]=number;
      }
    }
    //atomNumber = null; // Free unusefull resources
  }

  /** Create a Chemical model by parsing an input stream */
  XYZLatticeModel (InputStream is, boolean labl, boolean bx, boolean bnds, Color bgcolor, Color bndcolor, Color bxcolor) throws Exception
  {
    this();
    StreamTokenizer st;
    st = new StreamTokenizer(new BufferedInputStream(is, 4000));
    st.eolIsSignificant(true);
    st.commentChar('#');
    int slot = 0;

    this.label=labl;
    this.box=bx;
    this.bonds=bnds;
    this.br=bndcolor.getRed();
    this.bg=bndcolor.getGreen();
    this.bb=bndcolor.getBlue();
    this.gr=bgcolor.getRed();
    this.gg=bgcolor.getGreen();
    this.gb=bgcolor.getBlue();
    this.xr=bxcolor.getRed();
    this.xg=bxcolor.getGreen();
    this.xb=bxcolor.getBlue();
    atomTable = new Hashtable();
    defaultAtom = new ScalableAtomImpl(255, 100, 200, 1.0);
    try
    {
      scan:
      while (true)
      {
        switch ( st.nextToken() )
        {
          case StreamTokenizer.TT_EOF:
            break scan;
          default:
            break;
          case StreamTokenizer.TT_WORD:
            // get atom type
            String name = st.sval;
            if (name.equals("ATOM")) {
              // get name, RGB colour and size
              int r=255, g=255, b=255;
              double s=1.0;
              if (st.nextToken() == StreamTokenizer.TT_WORD)
              {
                name=st.sval;
                if (st.nextToken() == StreamTokenizer.TT_NUMBER)
                {
                  r = (int)st.nval;
                  if (st.nextToken() == StreamTokenizer.TT_NUMBER)
                  {
                    g = (int)st.nval;
                    if (st.nextToken() == StreamTokenizer.TT_NUMBER)
                    {
                      b =(int)st.nval;
                      if (st.nextToken() == StreamTokenizer.TT_NUMBER)
                        s = (double)st.nval;
                    }
                  }
                }
              }
              if (s>=2.0) s=2.0;
              if (s<0.0) s=1.0;
              atomTable.put(name.toLowerCase(), new ScalableAtomImpl(r, g, b, s));
            } else {
              // get position
              double x = 0, y = 0, z = 0;
              if (st.nextToken() == StreamTokenizer.TT_NUMBER)
              {
                x = st.nval;
                if (st.nextToken() == StreamTokenizer.TT_NUMBER)
                {
                  y = st.nval;
                  if (st.nextToken() == StreamTokenizer.TT_NUMBER)
                    z = st.nval;
                }
              }
              addVert(name, (float) x, (float) y, (float) z);
              // get connectivities
              while (st.nextToken() == StreamTokenizer.TT_NUMBER)
              {
                nbond++;
                bond[nbond][0]=nvert;
                bond[nbond][1]=(int)st.nval;
              }
            }
            while( st.ttype != StreamTokenizer.TT_EOL &&
                   st.ttype != StreamTokenizer.TT_EOF )
              st.nextToken();

        }   // end Switch

      }  // end while

      is.close();

    }  // end Try
    catch( IOException e) {}

    if (st.ttype != StreamTokenizer.TT_EOF)
      throw new Exception(st.toString());

  }  // end XYZLatModel()


  /** Add a vertex to this model */
  int addVert(String name, float x, float y, float z) {
    int i = nvert;
    if (i >= maxvert)
      if (vert == null) {
    maxvert = 100;
    vert = new float[maxvert * 3];
    atoms = new ScalableAtom[maxvert];
      } else {
        maxvert *= 2;
        float nv[] = new float[maxvert * 3];
        System.arraycopy(vert, 0, nv, 0, vert.length);
        vert = nv;
        ScalableAtom na[] = new ScalableAtom[maxvert];
        System.arraycopy(atoms, 0, na, 0, atoms.length);
        atoms = na;
      }
      ScalableAtom a = (ScalableAtom) atomTable.get(name.toLowerCase());
      if (a == null) a = defaultAtom;
      atoms[i] = a;
      i *= 3;
      vert[i] = x;
      vert[i + 1] = y;
      vert[i + 2] = z;
      return nvert++;
  }

  /** Transform all the points in this model */
  void transform() {
    if (transformed || nvert <= 0) return;
    if (tvert == null || tvert.length < nvert * 3)
      tvert = new int[nvert * 3];
    mat.transform(vert, tvert, nvert);
    transformed = true;
  }

// rŽcup?re les coordonnŽes des sommets dans le tableau vert
  void reinitCoord() {
    int index = 0;
    for(Iterator e = vVert.iterator(); e.hasNext(); ) {
      LatticeNodeGraph n = (LatticeNodeGraph) e.next();
      vert[index] = n.x();
      vert[index+1] = -n.y();
      vert[index+2] = n.z();
      index += 3;
    }
    // Accumuler le dŽcalage
    if((lgv.getX()!=0)||(lgv.getY() != 0)) {
      decalX -= lgv.getX();
      decalY -= lgv.getY();
      lgv.setX(0); lgv.setY(0);
      if(lgv.zoomCanvas() != null) {
        lgv.zoomCanvas().setDecalX(-decalX+lgv.getSize().width/2);
        lgv.zoomCanvas().setDecalY(-decalY);
        lgv.zoomCanvas().clearRect();
        lgv.zoomCanvas().refresh1();
      }
    }
  }

  /** Paint this model to a graphics context.  It uses the matrix associated
        with this model to map from model space to screen space.
        The next version of the browser should have double buffering,
        which will make this *much* nicer */
  void paint(Graphics g) {
    if (vert == null || nvert <= 0) return;
    reinitCoord(); // RŽcupŽrer les coordonnŽes des sommets
    transform(); // Appliquer la matrice de transformation
    draw(g);
  }

  /**
   * Draw
   */
  void draw(Graphics g) {
    Font largest = new Font("Geneva", Font.PLAIN, 18);
    Font large = new Font("Geneva", Font.PLAIN, 12);
    Font small = new Font("Geneva", Font.PLAIN, 10);
    Font smallest = new Font("Geneva", Font.PLAIN, 7);
    int v[] = tvert;
    int zs[] = ZsortMap;
    if (zs == null) {
      ZsortMap = zs = new int[nvert];
      for (int i = nvert; --i >= 0;)
        zs[i] = i * 3;
    }

        /*
    * I use a bubble sort since from one iteration to the next, the sort
    * order is pretty stable, so I just use what I had last time as a
    * "guess" of the sorted order.  With luck, this reduces O(N log N)
    * to O(N)
         */

    for (int i = nvert - 1; --i >= 0;) {
      boolean flipped = false;
      int a;
      int b;
      for (int j = 0; j <= i; j++) {
        a = zs[j];
        b = zs[j + 1];
        if (v[a + 2] > v[b + 2]) {
          zs[j + 1] = a;
          zs[j] = b;
          flipped = true;
        }
      }
      if (!flipped)  break;
    }

    int lg = 0;
    int lim = nvert;
    ScalableAtom ls[] = atoms;
    int drawn[] = new int[nbond+1];
    if (lim <= 0 || nvert <= 0)
      return;
    for (int i = 0; i < lim; i++) {
      int j = zs[i];
      int grey = v[j + 2];
      if (grey < 0)
        grey = 0;
      if (grey > 15)
        grey = 15;

      // draw bonds
      int v1, v2;
      boolean e = atoms[j/3].Exist();
      v1=j/3+1;
      if (((e)&&(bonds))||((!e)&&(box)))
      {
        for (int k=0; k<=nbond; k++)
        {
          v2=-1;
          if (bond[k][0]==v1)
            v2=bond[k][1]-1;
          if (bond[k][1]==v1)
            v2=bond[k][0]-1;
          if ((v2!=-1)&&(drawn[k]==0))
          {
            drawn[k]=1;
            double rr=(v[j+2]+v[v2*3+2]+6)/36.0;
            int r1,b1,g1;
            if (e) {
              r1=(int)(rr*(br-gr)+gr);
              b1=(int)(rr*(bb-gb)+gb);
              g1=(int)(rr*(bg-gg)+gg);
            } else {
              r1=(int)(rr*(xr-gr)+gr);
              b1=(int)(rr*(xb-gb)+gb);
              g1=(int)(rr*(xg-gg)+gg);
            }
            Color line = null;
            try {
              line = new Color(r1,g1,b1);
            }
            catch(Exception exc) {line = Color.lightGray;}
            g.setColor(line);
            g.drawLine(v[j]-decalX,v[j+1]-decalY,v[v2*3]-decalX,v[v2*3+1]-decalY);
          }
        }
      }
      if (e)
        atoms[j/3].paint(g, v[j]-decalX, v[j + 1]-decalY, grey);
      if (label) {
        //g.setColor(Color.black);
        //g.drawString(String.valueOf(v1), v[j], v[j+1]);
        g.setFont(new Font("Geneva", Font.PLAIN, grey));
        g.setColor(new Color(150-10*grey, 150-10*grey, 150-10*grey));
        /*if(grey>11) {
          //System.out.println("Largest");
          //g.setColor(Color.black);
          g.setFont(largest);
        }
        else {
          if(grey>8) {
            //System.out.println("Large");
            g.setColor(new Color(30, 30, 30));
            g.setFont(large);
          }
          else
            if(grey>5) {
            //System.out.println("small");
               g.setColor(new Color(100,100,100));
              g.setFont(small);
            }
            else {
            //System.out.println("smallest");
            g.setColor(new Color(150,150,150));
            g.setFont(smallest);
          }
        }*/
        //System.out.println(grey);
        FontMetrics fm = g.getFontMetrics();
        LatticeNodeGraph n = ((LatticeNodeGraph) vVert.get(v1-1));
        g.drawString(n.getLabel(), v[j]-decalX-fm.stringWidth(n.getLabel())/2, v[j+1]-decalY+fm.getMaxDescent());//+fm.getMaxDescent()
      }
    }
  }

  /** Find the bounding box of this model */
  void findBB() {
    if (nvert <= 0)
      return;
    float v[] = vert;
    float xmin = v[0], xmax = xmin;
    float ymin = v[1], ymax = ymin;
    float zmin = v[2], zmax = zmin;
    for (int i = nvert * 3; (i -= 3) > 0;) {
      float x = v[i];
      if (x < xmin)
        xmin = x;
      if (x > xmax)
        xmax = x;
      float y = v[i + 1];
      if (y < ymin)
        ymin = y;
      if (y > ymax)
        ymax = y;
      float z = v[i + 2];
      if (z < zmin)
        zmin = z;
      if (z > zmax)
        zmax = z;
    }
    this.xmax = xmax;
    this.xmin = xmin;
    this.ymax = ymax;
    this.ymin = ymin;
    this.zmax = zmax;
    this.zmin = zmin;
  }
}