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

import java.util.Vector;
/**
 * <p>Title: Galicia</p>
 * <p>Description: Galois Lattice Interactive Constructor</p>
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: University of Montreal</p>
 * @author David Grosser
 * @version 1.0
 */

/************************************************************
 * Le gestionnaire de magnétisme associé à un niveau donné
 ************************************************************/
class Magnetor extends ActionObject {

  Vector magnetableRelations; // Les relations magnétiques

  int ordonneLevel;// L'ordonnée des noeuds du niveau

// Constructor
  Magnetor(Magneto magneto, int level, int nbLevel, Vector magnetables, Vector magnetablesRelation) {
    super(magneto, level, nbLevel);
    init(magnetables, magnetablesRelation);
  }

  /**
   * Initialisation de l'ensemble des ééléments magnétiques
   */
  void init(Vector v1, Vector v2) {
    magnetables = new Vector();
    nbMagnetables = v1.size() + v2.size();
    for(int i=0; i<v1.size(); i++) {// Ajouter les noeuds magnétiques
      magnetables.add(v1.elementAt(i));
    }
    for(int j=0; j<v2.size(); j++) {// Ajouter les relations magnétiques
      magnetables.add(v2.elementAt(j));
    }
    if(magnetables.size()>0) ordonneLevel = getMagnetable(0).yCoord();
  }

/*protected boolean doAction(boolean threeDMode) {
  boolean testX = false;
  testX = doActionX();
  boolean testZ = false;
  //testZ = doActionZ();
  return (testX||testZ);
}*/

  /**
   * Magnétisme sur un niveau donné selon l'axe X
   */
  protected boolean doAction(boolean threeDMode) {
    if(! magneto.getMagnet()) return false;
    /*if(isFixedLevel()) {
      for(int i=0; i<nbMagnetables; i++) {getMagnetable(i).setIsMagnetable(false);}
      return false;
    }*/
    boolean deplacement = false; // Aucun noeud encore déplacé pour cette itération
    if(magnetables.size()>0) {
      ordonneLevel = getMagnetable(0).yCoord();
    }
    for(int i=0; i<nbMagnetables; i++) {// Pour chaque noeud du niveau
      Magnetable n = getMagnetable(i);
      if((n instanceof MagnetableRelation)&&(! magneto.magnetRelation())) {;}
      else {
        //if(n instanceof MagnetableRelation) System.out.println(n+" est une relation");
        if(n.isMagnetable()) {// Le magnetable subit-il le magnétisme ?
          int decalX = 0;
          int decalZ = 0;
          if(Math.abs(ordonneLevel-n.yCoord())<10) {
            decalX = repulsionX(n);
            if(threeDMode) decalZ = repulsionZ(n);
            //if(decalX>0) deplacement = true;
          }
          //double tensionX = n.tensionX(true);
          double tensionX = (int) (magneto.getTensionFactor()*n.tensionX(true));
          //if(tensionX > 10) tensionX = 10;
          //if(tensionX < -10) tensionX = -10;
          double tensionZ = 0;
          if(threeDMode) {
            tensionZ = (int) (magneto.getTensionFactor()*n.tensionZ(true));
            //if(tensionZ > 10) tensionZ = 10;
            //if(tensionZ < -10) tensionZ = -10;
          }
          int decalY = decalY(n);
          //if(tensionX != 0) {
            decalX += (int) tensionX;
            if(threeDMode) decalZ += (int) tensionZ;
            n.move(decalX, decalY, decalZ);
            if((decalX != 0)||(decalY != 0)||(decalZ != 0)) deplacement = true;
          //}
          //if((Math.abs(decalY)<3)&&repulsion(n)) deplacement = true;
        }
      }
    }
    return deplacement;
  }

  int decalY(Magnetable n) {
    if(n.yCoord() != ordonneLevel) {
      int decalY = (ordonneLevel-n.yCoord())/5;
      if(Math.abs(decalY) <= 1) decalY = (ordonneLevel-n.yCoord());
      return decalY;
    }
    else return 0;
  }

  int repulsionX(Magnetable n) {
    //if(! collision) return false;
    int pression = pressionX(n);
    int decal = (int) Math.round(((double) pression) * magneto.getRepulsionFactor());
    //int decal = pression;
    //if(decal != 0) {
      //n.move(decal, 0);
    //if(decal > 10) decal = 10;
    //if(decal < -10) decal = -10;
      return decal;// Présence d'une collision
    //}
    //return false;
  }

  /**
   * Calcul de la pression exercée sur un magnetable n
   * par les autres magnetables. Cette pression est exprimée sous
   * la forme d'un décalage en pixels
   */
  public int pressionX(Magnetable n) {
    int pression = 0;
    //if(! collision) return 1; // On ne gère pas les collisions
    Magnetable noeud = null; // Un noeud du niveau
    int cl = (int) (magneto.getcLargeur(nbMagnetables)*1.3);
    int ch = magneto.getcHauteur()/3;
    int unlink = cl / 3;
    int decal = 0;

// Pression de la souris quand elle est magnétisée
    if((magneto.magnetMouse)&&(Math.abs(ordonneLevel - y)<ch)) {
      if(x >= n.xCoord()) {//CollisionD avec la souris
        decal = x - n.xCoord() - cl;
        if(n.xCoord()+cl > x) pression += decal - (decal * (Math.abs(ordonneLevel - y))/ch);
      }
      if(x < n.xCoord()) {//CollisionG avec la souris
        decal = n.xCoord() - x - cl ;
        if(n.xCoord() - cl < x) pression -= decal - (decal * (Math.abs(ordonneLevel - y))/ch);
      }
    }

// Magnetisme des bordures
    //if((0 < n.xCoord())&&((n.xCoord() - cl) < 0)) pression -= n.xCoord() - cl;

// Pression des autres magnetables
    for(int i=0; i < nbMagnetables; i++) {
      noeud = getMagnetable(i);
      double dz = Math.abs(noeud.zCoord()-n.zCoord());
      double dx = Math.abs(noeud.xCoord() - n.xCoord());
      decal = (int) dx - cl;
      if((active(noeud))&&(dz<cl)) {
       //decal = (int) Math.sqrt(Math.pow((noeud.xCoord()-n.xCoord()), 2.0)+Math.pow((noeud.zCoord()-n.zCoord()), 2.0)) - cl;
        //decal = noeud.xCoord() - n.xCoord() - cl;
        //decal = (int) dx - cl;
        if((noeud.xCoord() >= n.xCoord())&&(noeud != n)) {//CollisionD
          //decal = (int) dx - cl;
          int pressionInverse = pressionInverseX(n, noeud, cl);
          //int pressionInverse = pressionInverseX(n, noeud, cl-Math.abs(noeud.zCoord()-n.zCoord()));
          //pression -= pressionInverse;
          //if(pressionInverse != 0) return pressionInverse;
          if(pressionInverse != 0) pression -= pressionInverse;
          else if(n.xCoord()+cl > noeud.xCoord()) pression += decal*noeud.repulsion(); // On augmente la pression (décalage à droite)
        }// Fin collisionD
        if(noeud.xCoord() < n.xCoord()) {//CollisionG
          //decal = (int) - dx - cl ;
          int pressionInverse = pressionInverseX(noeud, n, cl);
          if(pressionInverse != 0) {;}
          //if(((noeud.xCoord() - n.xCoord()) < unlink) &&
          //   (noeud.tensionX() >= n.tensionX())) pression -= unlink;//Gestion de la répulsion inverse : dénouer les liens
          //if(((n.xCoord() - noeud.xCoord())< unlink) && (noeud.tensionX() >= n.tensionX())) pression = unlink - 10;//Gestion de la répulsion inverse : dénouer les liens
          else if(n.xCoord() - cl < noeud.xCoord()) pression -= decal*noeud.repulsion(); // On diminue la pression (décalage à gauche), au proratat du facteur de repulsion exercé par n
        }
      }
    }
    //if(pression == 0) return 1;
    //decal = (int) Math.round(((double) (colD - colG)) * repulsionFactor);
    //if(pression <= smooth) pression = 0;// adoucir les vibrations
    return pression;
  }

// Retourne true si le magnetable est un repulseur
boolean active(Magnetable m) {
  if(m instanceof MagnetableRelation) {
    if(! magneto.magnetRelation()) return false;
  }
  else if(Math.abs(ordonneLevel - m.yCoord())>10) return false;
  return true;
}

  /**
   * Calcul de la pression inverse
   * Lorsque deux magnétables sont très proches, ils peuvent changer de place
   * noeud.xCoord() >= n.xCoord() et n != noeud
   */
 /*  public int pressionInverse(Magnetable n, Magnetable noeud, int cl) {
     int unlink = cl/3;
     //int unlink = (cl/3) * n.repulsionX();
     int unlink2 = (cl/6) ;
     //int unlink2 = cl/6 * n.repulsionX();
     boolean inZone1 = ((noeud.xCoord() - n.xCoord()) < unlink);
     boolean inZone2 = ((noeud.xCoord() - n.xCoord()) > unlink2);
     if(inZone1) {
     //if(inZone2) return 0;
     //else
         if(noeud.tensionX() < n.tensionX()) return (noeud.xCoord() - n.xCoord()) * 2;
     }
     return 0;
   }*/
  public int pressionInverseX(Magnetable n, Magnetable noeud, int cl) {
    if(true) return 0;
    int unlink = cl/3;
    //int unlink = (cl/3) * n.repulsionX();
    int unlink2 = (cl/6) ;
    //int unlink2 = cl/6 * n.repulsionX();
    boolean inZone1 = ((noeud.xCoord() - n.xCoord()) < unlink);
    //boolean inZone1 = ((noeud.xCoord() - n.xCoord()) < unlink);
    boolean inZone2 = ((noeud.xCoord() - n.xCoord()) > unlink2);
    if(inZone1) {
      if(inZone2) return 0;
      //else
      if(noeud.tensionX(true) < n.tensionX(true)) //return (noeud.xCoord() - n.xCoord()) * 2;
        //return (int) (((double) unlink) * n.repulsionX());
        return (int) (2*((double) unlink));
    }
    return 0;
  }

  /**
   * Magnétisme sur un niveau donné selon l'axe Z
   */
//  protected boolean doActionZ() {
//    if(! magneto.getMagnet()) return false;
    /*if(isFixedLevel()) {
      for(int i=0; i<nbMagnetables; i++) {getMagnetable(i).setIsMagnetable(false);}
      return false;
    }*/
/*    boolean deplacement = false; // Aucun noeud encore déplacé pour cette itération
    if(magnetables.size()>0) {
      ordonneLevel = getMagnetable(0).yCoord();
    }
    for(int i=0; i<nbMagnetables; i++) {// Pour chaque noeud du niveau
      Magnetable n = getMagnetable(i);
      if((n instanceof MagnetableRelation)&&(! magneto.magnetRelation())) {;}
      else {
        //if(n instanceof MagnetableRelation) System.out.println(n+" est une relation");
        if(n.isMagnetable()) {// Le magnetable subit-il le magnétisme ?
          int decalZ = 0;
          if(Math.abs(ordonneLevel-n.yCoord())<10) {
            decalZ = repulsionZ(n);
            //if(repulsionZ(n)) deplacement = true;
          }
          double tensionZ = n.tensionZ(true);
          if(tensionZ != 0) {
            decalZ += (int) (magneto.getTensionFactor()*tensionZ);
            n.move(0, 0, decalZ);
            if(decalZ != 0) deplacement = true;
          }
          //if((Math.abs(decalY)<3)&&repulsion(n)) deplacement = true;
        }
      }
    }
    return deplacement;
  }*/

  int repulsionZ(Magnetable n) {
    //if(! collision) return false;
    int pression = pressionZ(n);
    int decal = (int) Math.round(((double) pression) * magneto.getRepulsionFactor());
    //int decal = pression;
    //if(decal != 0) {
      //n.move(0, 0, decal);
    //if(decal > 10) decal = 10;
    //if(decal < -10) decal = -10;
      return decal;
      //return true;// Présence d'une collision
    //}
    //return false;
  }

  /**
   * Calcul de la pression exercée sur un magnetable n
   * par les autres magnetables. Cette pression est exprimée sous
   * la forme d'un décalage en pixels
   */
  public int pressionZ(Magnetable n) {
    int pression = 0;
    //if(! collision) return 1; // On ne gère pas les collisions
    Magnetable noeud = null; // Un noeud du niveau
    int cl = (int) (magneto.getcLargeur(nbMagnetables)*1.3);
    //int ch = magneto.getcHauteur()/3;
    int unlink = cl / 3;
    int decal = 0;

// Pression des autres magnetables
    for(int i=0; i < nbMagnetables; i++) {
      noeud = getMagnetable(i);
      double dx = Math.abs(noeud.xCoord() - n.xCoord());
      double dz = Math.abs(noeud.zCoord() - n.zCoord());
      decal = (int) dz - cl;
      if((active(noeud))&&(dx<cl)) {
        //decal = noeud.zCoord() - n.zCoord() - cl;
        if((noeud.zCoord() >= n.zCoord())&&(noeud != n)) {//CollisionD
          //decal = (int) dz - cl;
          //decal = (int) Math.sqrt(dz*dz+dx*dx) - cl;
          int pressionInverse = pressionInverseZ(n , noeud, cl);
          //pression -= pressionInverse;
          //if(pressionInverse != 0) return pressionInverse;
          if(pressionInverse != 0) pression -= pressionInverse;
          else if(n.zCoord()+cl > noeud.zCoord()) pression += decal*noeud.repulsion(); // On augmente la pression (décalage à droite)
        }// Fin collisionD
        if(noeud.zCoord() < n.zCoord()) {//CollisionG
          //decal = (int) - Math.sqrt(dz*dz+dx*dx) - cl ;
          int pressionInverse = pressionInverseZ(noeud , n, cl);
          if(pressionInverse != 0) {;}
          //if(((noeud.xCoord() - n.xCoord()) < unlink) &&
          //   (noeud.tensionX() >= n.tensionX())) pression -= unlink;//Gestion de la répulsion inverse : dénouer les liens
          //if(((n.xCoord() - noeud.xCoord())< unlink) && (noeud.tensionX() >= n.tensionX())) pression = unlink - 10;//Gestion de la répulsion inverse : dénouer les liens
          else if(n.zCoord() - cl < noeud.zCoord()) pression -= decal*noeud.repulsion(); // On diminue la pression (décalage à gauche), au proratat du facteur de repulsion exercé par n
        }
      }
    }
    //if(pression == 0) return 1;
    //decal = (int) Math.round(((double) (colD - colG)) * repulsionFactor);
    //if(pression <= smooth) pression = 0;// adoucir les vibrations
    return pression;
  }

  /**
   * Calcul de la pression inverse
   * Lorsque deux magnétables sont très proches, ils peuvent changer de place
   * noeud.xCoord() >= n.xCoord() et n != noeud
   */
  public int pressionInverseZ(Magnetable n, Magnetable noeud, int cl) {
    if(true) return 0;
    int unlink = cl/3;
    //int unlink = (cl/3) * n.repulsionX();
    int unlink2 = (cl/6) ;
    //int unlink2 = cl/6 * n.repulsionX();
    boolean inZone1 = ((noeud.zCoord() - n.zCoord()) < unlink);
    //boolean inZone1 = ((noeud.xCoord() - n.xCoord()) < unlink);
    boolean inZone2 = ((noeud.zCoord() - n.zCoord()) > unlink2);
    if(inZone1) {
      if(inZone2) return 0;
      //else
      if(noeud.tensionZ(true) < n.tensionZ(true)) //return (noeud.xCoord() - n.xCoord()) * 2;
        //return (int) (((double) unlink) * n.repulsionX());
        return (int) (2*((double) unlink));
    }
    return 0;
  }

} // Fin MagnetoLevel