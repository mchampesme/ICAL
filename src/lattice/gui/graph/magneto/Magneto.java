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

package lattice.gui.graph.magneto;

import java.awt.event.MouseEvent;
import java.awt.event.MouseMotionListener;
import java.util.Iterator;
import java.util.Vector;

import lattice.gui.graph.LatticeGraphViewer;

/**
 * <p>Title: Galicia</p>
 * <p>Description: Galois Lattice Interactive Constructor</p>
 * Thread pour gérer le déplacement des noeuds en fonction des contraintes magnétiques,
 * on cherche à minimiser la longueur des relations d'un noeud. Si la repulsion
 * est activée, chaque noeud observe la proximité des noeuds, calcule une force de répulsion et se déplace en conséquence
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: University of Montreal</p>
 * @author David Grosser
 * @version 1.0
 */

public class Magneto extends Thread implements MouseMotionListener {

  public  LatticeGraphViewer lgv; // Le grapher

  public long timeSleep = 50; // Durée de rafraichissement en millisecondes (sleep du thread)
  public boolean active = false; // this actif
  public boolean magnet = false;
  public double tensionFactor = 10.0;
  public double repulsionFactor = 0.5;// O, pas de répulsion
  //public int unlink = 30;
  //public int smooth = 3;

  public boolean fixFirstLevel = false; // Ne pas magnétiser le premier niveau
  public boolean fixLastLevel = false; // Ne pas magnétiser le dernier niveau
  //public boolean fixBottom = true; // Magnétisme du bottom
  public boolean magnetRelation = false; // Magnetisme des relations
  public boolean magnetMouse = false; // Magnetisme de la souris
  //public boolean rotation = false; // Rotation
  public float rotation = 0f;
  protected Vector vAction; // Le vecteur contenant les Actionobjects par niveau
  protected Magnetable top, bottom;
// Constructeur
  public Magneto(LatticeGraphViewer lgv) {
    this.lgv = lgv;
  }

  public boolean getMagnet() {
    return magnet;
  }

  public void setMagnet(boolean b) {
    magnet = b;
    if(b) active = true;
  }

  public double getRepulsionFactor() {
    return repulsionFactor;
  }

  public void setRepulsionFactor(double d) {
    repulsionFactor = d;
  }

  public double getTensionFactor() {
    return tensionFactor;
  }

  public void setTensionFactor(double d) {
    tensionFactor = d;
  }

/*  public int getUnlink() {
    return unlink;
  }

  public void setUnlink(int d) {
    unlink = d;
  }*/

  public long getTimeSleep() {
    return timeSleep;
  }

  public void setTimeSleep(long l) {
    timeSleep = l;
  }

  public boolean fixFirstLevel() {
    return fixFirstLevel;
  }

  public void setFixFirstLevel(boolean b) {
    ((ActionObject) vAction.get(2)).fix(b);
    fixFirstLevel = b;
  }

  public boolean fixLastLevel() {
    return fixLastLevel;
  }

  public void setFixLastLevel(boolean b) {
    ((ActionObject) vAction.get(vAction.size()-3)).fix(b);
     fixLastLevel = b;
  }

/*  public boolean fixBottom() {
    return fixBottom;
  }

  public void setFixBottom(boolean b) {
    fixBottom = b;
  }*/

  public boolean magnetRelation() {
    return magnetRelation;
  }

  public void setMagnetRelation(boolean b) {
    magnetRelation = b;
  }

  public boolean magnetMouse() {
    return magnetMouse;
  }

  public void setMagnetMouse(boolean b) {
    magnetMouse = b;
  }

  public float getRotation() {
    return rotation;
  }

  public void setRotation(float val) {
    rotation = val;
    if(rotation != 0) active = true;
  }

  /**
   * Activation du magnétisme
   */
  public void run() {
    while(true) {
      try {
        Thread.sleep(timeSleep);
        } catch(InterruptedException e) {System.out.println("Magneto Interruption");}
        if(active) {
          if(vAction == null) buildvNiveau();
          //if((lgv.getX() != 0)&&(lgv.getY() != 0))
          boolean repaint = false;
            if((lgv.getThreeD())&&(rotation != 0)) {
              lgv.rotation(rotation);
              repaint = true;
            }
            synchronized(lgv) {if(incAction()) repaint = true;} // Magnétiser les niveaux
            if(repaint) synchronized(lgv) {lgv.repaint();}
            //else if(incAction()) lgv.repaint();
        }
    }
  }

  /**
   * Désactivation
   */
  public void stopper() {
    active = false;
  }

  /**
   * Gestion d'une itération
   * Pour chaque niveau autre que top et bottom
   */
  public boolean incAction() {
    boolean deplacement = false;
    if(lgv.getNbNiveau() > 2) {
      //int firstLevel = 1;
      //if(fixFirstLevel) firstLevel = 2;
      //int lastLevel = lgv.getNbNiveau() - 2;
      //if(fixLastLevel) lastLevel = lgv.getNbNiveau() - 3;
      //for(int i=firstLevel; i<=lastLevel; i++) // Pour tout les niveaux concernés
      ActionObject ao;
      for(Iterator i=vAction.iterator(); i.hasNext();) {
        ao = ((ActionObject) i.next());
        /*if(lgv.getThreeD()) {
          double random = Math.random();
          if(random < 0.5) {
            if(ao.doActionZ()) deplacement = true;
            if(ao.doActionX()) deplacement = true;
          }
          else {
            if(ao.doActionX()) deplacement = true;
            if(ao.doActionZ()) deplacement = true;
          }
        }*/
        if(ao.doAction(lgv.getThreeD())) deplacement = true; // Une itération en X sur le niveau
        //if((lgv.getThreeD())&&(ao.doActionZ())) deplacement = true; // Une itération en Z sur le niveau
      }
    }
    //if(! deplacement) collision = true;
    return deplacement; // True si un noeud déplacé
  }

  public ActionObject getNiveau(int i) {
    return (ActionObject) vAction.elementAt(i);
  }

// Retourne la largeur désiré entre noeuds
  public int getcLargeur(int i) {
    return lgv.getcLargeur(i);
  }

// Retourne la hauteur entre noeuds
  public int getcHauteur() {
    return lgv.getcHauteur();
  }

  /**
   * Construire le vecteur de niveau. Appelé 1 fois à l'initialisation
   * Initialisation du top
   */
  public void buildvNiveau() {
    vAction = new Vector(); // Le vecteur contenant les instances de MagnetoLevel
    Vector v1 = lgv.getNiveau();
    Vector v2 = lgv.getNiveauRelation();// les relations magnétiques
    this.top = (Magnetable) (((Vector) v1.elementAt(0)).elementAt(0));
    this.top.setIsMagnetable(false);
    this.bottom = (Magnetable) (((Vector) v1.elementAt(v1.size()-1)).elementAt(0));
    this.bottom.setIsMagnetable(false);
    Magnetor ml = null;
    int nbLevel = v1.size();
    for(int i=0; i<nbLevel; i++) {
      vAction.add(new Magnetor(this, i, nbLevel, (Vector) v1.elementAt(i), (Vector) v2.elementAt(i)));
      //vAction.add(new Rotator2(this, i, nbLevel, (Vector) v1.elementAt(i)));
    }
    //vAction.add(new Rotator2(this, 1, nbLevel, (Vector) v1.elementAt(1)));
  }

  public void mouseMoved(MouseEvent e) {
    if(vAction != null)
       for(int i=0; i<vAction.size(); i++) {
         ((ActionObject) vAction.elementAt(i)).setMousePosition(e.getX(), e.getY());
       }
  }

  public void mouseDragged(MouseEvent e) {;}

  /*public Dimension getSize() {
    return lgv.getSize();
  }*/

}