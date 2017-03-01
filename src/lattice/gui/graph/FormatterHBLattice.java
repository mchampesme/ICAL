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

package lattice.gui.graph;

// import java
import java.awt.Color;
import java.awt.Point;
import java.awt.Rectangle;
import java.util.TreeSet;
import java.util.Vector;

import lattice.graph.trees.Noeud;
import lattice.graph.trees.formatter.Formatter;
import lattice.gui.graph.magneto.MagnetableRelation;
/**
 * <p>Titre : Lattice</p>
 * <p>Description : Manipulation des treillis</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : Université de Montréal</p>
 * @author David Grosser
 * @version 1.0
 */

public class FormatterHBLattice extends Formatter {

  public final static int DIST_FROM_TOP = 10; // Distance depuis le haut de la fenetre du Top

  public  int cLargeur = 140;
  public  int cHauteur = 100;

  protected Rectangle rectParent;
  //public  int cl ;
  //public  int ch ;
  protected int maxElement = -1; // Nbre de noeuds du niveau qui en a le plus
  public Vector vNiveau, vNiveauRelation;
  public int nbNiveau = 0;
  public boolean fitScreen = false;
  public boolean optimizerOrdre = false;
  public boolean keepOrder = false;
  public boolean init = true;
  public LatticeGraphViewer lgv;

  public FormatterHBLattice(Vector noeuds, Rectangle rectParent, int zoom, boolean fitScreen) {
    super(noeuds);
    this.rectParent = rectParent;
    this.zoom = zoom;
    this.fitScreen = fitScreen;
  }

  public FormatterHBLattice(LatticeGraphViewer lgv, Rectangle rectParent, int zoom, boolean fitScreen) {
    this(lgv.noeuds, rectParent, zoom, fitScreen);
    this.lgv = lgv;
  }

  public int getNbNiveau() {
    return nbNiveau;
  }

  public int getcLargeurRel() {
    return (int) (((float) cLargeur) * ((float) zoom)/10.0f);
  }

  public int getcHauteurRel() {
    return (int) (((float) cHauteur)  * ((float) zoom)/10.0f);
  }

  protected void effacerNiveau() {
    for(int i=0; i<noeuds.size(); i++)
      ((LatticeNodeGraph) noeuds.elementAt(i)).setNiveau(-1);
    vNiveau = null;
  }

  // Initialisation des contraintes de hauteur et de largeur
  public void initContraintes(LatticeNodeGraph top) {
    setCl(getcLargeurRel());
    if(fitScreen) {
      Vector f = feuilles(top);
      LatticeNodeGraph bottom = (LatticeNodeGraph) f.elementAt(0);
      nbNiveau = bottom.getNiveau();
      setCh((rectParent.height-DIST_FROM_TOP) / (nbNiveau+1));
    }
    else setCh(getcHauteurRel());
  }

// Surcharge
public void formatter(Noeud unNoeud) {
  if(init) formatterInit(unNoeud); // Lorsqu'on format pour la 1ere fois
  else if(optimizerOrdre) formatterSecond(unNoeud);
  //else formatterSecond(unNoeud); // Lorsque l'on a déjà formatté
       else formatterInit(unNoeud);
  init = false;
}

// Surcharge
  public void formatterInit(Noeud unNoeud) {
    initContraintes((LatticeNodeGraph) unNoeud);
    effacerNiveau();// Effacer le vecteur de niveau et le niveau associé à chaque noeud
    maxElement = -1;
    demarquer() ;
    unNoeud.setPosSup(new Point(rectParent.width/2 - 15, DIST_FROM_TOP));
    ((LatticeNodeGraph) unNoeud).setNiveau(0);
      vNiveau = new Vector();
      vNiveauRelation = new Vector();
      formatterYNiveau((LatticeNodeGraph) unNoeud, 0);
      buildvNiveau();// Construire le vecteur de niveau
      //System.out.println(vNiveauRelation);
    //}
    //else positionneYNiveau((LatticeNodeGraph) unNoeud);

    //LatticeNodeGraph bottom = ((LatticeNodeGraph) (feuille(unNoeud).elementAt(0)));
    //affVectorNiv();
    formatterXNiveau((LatticeNodeGraph) unNoeud);
  }

// Lorsque l'on a déjà formatté et que les variables sont déjà initialisées
  public void formatterSecond(Noeud unNoeud) {
    //initContraintes((LatticeNodeGraph) unNoeud);
    //effacerNiveau();// Effacer le vecteur de niveau
    //maxElement = -1;
    //demarquer() ;
    //demarquer2() ;
    //unNoeud.setPosSup(new Point(rectParent.width/2 - 15, DIST_FROM_TOP));
    //((LatticeNodeGraph) unNoeud).setNiveau(0);
      //vNiveau = new Vector();
      //formatterYNiveau((LatticeNodeGraph) unNoeud, 0);
      //buildvNiveau();// Construire le vecteur de niveau
    //}
    //else
    unNoeud.setPosSup(new Point(rectParent.width/2 - 15, DIST_FROM_TOP));
    positionneYNiveau((LatticeNodeGraph) unNoeud);

    //LatticeNodeGraph bottom = ((LatticeNodeGraph) (feuille(unNoeud).elementAt(0)));
    //affVectorNiv();
    formatterXNiveau((LatticeNodeGraph) unNoeud);
  }


  /**
   * Positionne la coordonnées Y de chaqued noeuds
   * Le vecteur de niveau est déjà construit
   */
  public void positionneYNiveau(LatticeNodeGraph top) {
    LatticeNodeGraph uneFeuille = null;
    int h = top.y();
    for(int i = 1; i < vNiveau.size() ; i++) {
      h += ch;
      Vector vi = (Vector) vNiveau.elementAt(i);
      for(int j=0; j<vi.size(); j++) {
        uneFeuille = (LatticeNodeGraph) vi.elementAt(j) ;
        uneFeuille.setPosSup(new Point(0, h));
      }
    }
  }

  /**
   * Positionner les niveaux en Y
   * Pas de connaissance préalable sur les noeuds
   */
  public void formatterYNiveau(LatticeNodeGraph unNoeud, int niv) {
    Vector v = unNoeud.fils();
    LatticeNodeGraph uneFeuille = null;
    //int h = calcH(unNoeud);
    int h = ch + unNoeud.y();
    niv += 1;
    if(v.size() == 0) nbNiveau = niv;
    for(int i=0; i<v.size(); i++) {
      uneFeuille = (LatticeNodeGraph) v.elementAt(i) ;
      if(uneFeuille.getNiveau() < niv) {
        uneFeuille.setPosSup(new Point(0, h));
        uneFeuille.setNiveau(niv);
        formatterYNiveau(uneFeuille, niv);
      }
    }
  }

  /**
   * Calcul de l'écart horizontal entre les noeuds relativement au nombre de noeuds
   * du niveau. Si beaucoup de noeuds, écart plus petit
   */
  public int calcRel(int nbElement) {
    int cl2 = getcLargeurRel();
    int clRel = cl2 - 5*nbElement;
    if(clRel<(cl2/2)) cl = cl2/2; else cl = clRel;
    return cl;
  }

  public int calcX(LatticeNodeGraph top, int nbElement) {
    if(fitScreen) cl = rectParent.width / nbElement;
    else {//if(nbElement >= 5)
      calcRel(nbElement); // Calcul du cl relatif
    }
    return top.x() + cl/2 - (cl * nbElement)/ 2; // Coord X de chaque premier fils
  }

  public int incX() {
    return cl;
  }

  /**
   * Ordonner les noeuds horizontalement par niveau
   */
  public void formatterXNiveau(LatticeNodeGraph top) {
    Vector noeuds = new Vector();
    LatticeNodeGraph uneFeuille = null;
    Vector vNiveauNiv = null;
    int niv = 1;
    int pX = 0;
    for(int niveau = niv; niveau < nbNiveau; niveau++) {// Pour chaque niveau
      vNiveauNiv = getNiveau(niveau); // Récupérer les noeuds situé au "niveau"
      //vNiveauNiv = ordonner(vNiveauNiv, top, niveau); // Ordonner la premi?re rangée de fils
      //int pX = rectParent.width/2 + cl/2 - (cl * vNiveauNiv.size())/ 2; // Coord X de chaque premier fils
      //int pX = top.x() + cl/2 - (cl * vNiveauNiv.size())/ 2; // Coord X de chaque premier fils
      pX = calcX(top, vNiveauNiv.size());
      for(int i = 0 ; i< vNiveauNiv.size(); i++) { // Pour chaque noeud d'un niveau
        uneFeuille = (LatticeNodeGraph) vNiveauNiv.elementAt(i) ;
        uneFeuille.setPosSup(new Point(pX, uneFeuille.y()));
        pX += incX();
      }
      if(optimizerOrdre) {
        //System.out.println("Sans fils, Niveau"+niveau);
        minCrossing(getNiveau(niveau), false);
      }
    }
    if(optimizerOrdre) {
      for(int niveau = niv; niveau < nbNiveau; niveau++) {
        //System.out.println("Avec Fils, Niveau"+niveau);
        minCrossing(getNiveau(niveau), true);
      }
      //noeuds.addAll(minimizeCrossing(vNiveauNiv));
    }
    //if((optimizerOrdre)&&(lgv != null)) {lgv.noeuds = noeuds;}
  }

public Vector getvNiveau() {
  return vNiveau;
}

public Vector getvNiveauRelation() {
  return vNiveauRelation;
}

  public Vector getNiveau(int i) {
    return (Vector) vNiveau.elementAt(i);
  }

  /**
   * Construction du vecteur contenant les vecteurs de niveau
   * Chaque vecteur de niveau contient des objets qui sont magnétisables
   */
  public void buildvNiveau() {
    for(int i = 0; i<nbNiveau; i++) {
      vNiveauRelation.add(new Vector());
      vNiveau.add(buildvNiveau(i));
    }
  }

  public Vector buildvNiveau(int niv) {
    Vector v = new Vector();
    LatticeNodeGraph noeud = null;
    for(int i=0; i<noeuds.size(); i++) {
      noeud = (LatticeNodeGraph) noeuds.elementAt(i);
      if(noeud.getNiveau() == niv) {
        v.addElement(noeud);
        buildvNiveauRelation(noeud, niv);
      }
    }
    return v;
  }

  /**
   * Construit l'ensemble des objets magnétiques associés aux relations
   */
  public void buildvNiveauRelation(LatticeNodeGraph noeud, int niv) {
    LatticeRelation lr = null;
    for(int i=0; i<noeud.nbRelationArrive(); i++) {
      lr = (LatticeRelation) (noeud.relationArrive(i));
      int niv2 = ((LatticeNodeGraph) lr.origine()).getNiveau();
      int diffNiv = niv - niv2;
      if(diffNiv > 1) { // La relation est candidate (cross relation)
        Color bgColor = LatticeRelation.NORMAL_COLOR.brighter();
        for(int j=1; j < diffNiv; j++) {
          lr.setBgColor(bgColor);// Plus la relation traverse un nombre élevé de niveau, plus elle est claire
          MagnetableRelation mr = new MagnetableRelation(lr, diffNiv, j);
          ((Vector) vNiveauRelation.elementAt(niv2+j)).add(mr);
          bgColor = new Color(Math.min(bgColor.getRed()+20,200), Math.min(bgColor.getGreen()+20,200), Math.min(bgColor.getBlue()+20,200));
        }
      }
    }
  }

  /**
   * Ordonner les niveaux
   */
  public Vector ordonner(Vector v, LatticeNodeGraph top, int niv) {
    if(optimizerOrdre) {
      if(niv == 1) return v;//ordonnerFirst(v, top);
      else return ordonnerOther(v);
    }
    //else*/
    return v;
  }

  /**
   * Ordonner le premier niveau
   */

  public Vector ordonnerFirst(Vector v, LatticeNodeGraph top) {
    int pX = 0;
    LatticeNodeGraph uneFeuille = null;
    pX = calcX(top, v.size());
    for(int i = 0 ; i< v.size(); i++) { // Pour chaque noeud du premier niveau
      uneFeuille = (LatticeNodeGraph) v.elementAt(i) ;
      uneFeuille.setPosSup(new Point(pX, uneFeuille.y()));
      pX += incX();
    }
    return v;
  }

  /**
   * Ordonner un niveau
   */

  public Vector ordonnerOther(Vector v) {
    TreeSet vTreeSet = new TreeSet();
    LatticeNodeGraph noeud;
    LatticeNodeGraph unPere;
    int sommeX = 0;
    for(int i = 0; i<v.size(); i++) {
      noeud = (LatticeNodeGraph) v.elementAt(i);
      Vector vPere = peres(noeud);
      //System.out.println(vPere);
      sommeX = 0;
      for(int j = 0; j<vPere.size(); j++) {
        unPere = (LatticeNodeGraph) vPere.elementAt(j);
        sommeX += unPere.x();
      }
      noeud.setX(sommeX/vPere.size());
      vTreeSet.add(noeud);
    }
    return new Vector(vTreeSet);
    //return new Vector(vTreeSet);
  }

  /**
   * Ordonner un niveau de mani?re à minimiser les croisements des relations
   */
/*  public Vector minimizeCrossing(Vector v) {
    int nbtotal = minCrossing(v);
    //int nbtotal2 = 0;
    //while(true) {
      //nbtotal2 = minCrossing(v);
     // System.out.println("nbtotal = "+nbtotal+" nbtotal2 = "+nbtotal2);
      //if(nbtotal == nbtotal2) return v;
      //else {System.out.println("On continue");}
      //if(nbtotal < nbtotal2) {
      //  System.out.println("Bizarre, avant :"+nbtotal+" apr?s : "+nbtotal2);
      //  return v;
      //}
      return v;
    //}
  }*/

// One pass
  public int minCrossing(Vector v, boolean fils) {
    boolean test = false;
    LatticeNodeGraph noeud1, noeud2;
    int nbTotal = 0;
    int nbCrossing1 = 0;
    int nbCrossing2 = 0;
 //   for(int i = 0; i<v.size(); i++) {
    int i = 0;
    int j = 0;
    while(i<v.size()) {
      if(test) {i = 0;}
      test = false;
      noeud1 = (LatticeNodeGraph) v.elementAt(i);
      j = i+1;
      //for(int j = i+1; j<v.size(); j++) {
      while(j<v.size()) {
        noeud2 = (LatticeNodeGraph) v.elementAt(j);

        nbCrossing1 = nbCrossing(peres(noeud1), peres(noeud2)); // noeud1 à gauche de noeud2
        //System.out.println("Peres : Test sur "+noeud1+","+noeud2+" nb croisements = "+nbCrossing1);
        nbCrossing2 = nbCrossing(peres(noeud2), peres(noeud1)); // noeud2 à gauche de noeud1
        //System.out.println("Peres : Test sur "+noeud2+","+noeud1+" nb croisements = "+nbCrossing2);
        //if((fils)&&(nbCrossing1 == nbCrossing2)) {
        if(fils) {
            nbCrossing1 += nbCrossing(noeud1.fils(), noeud2.fils());
            //System.out.println("Fils : Test sur "+noeud1+","+noeud2+" nb croisements = "+nbCrossing1);
            nbCrossing2 += nbCrossing(noeud2.fils(), noeud1.fils());
            //System.out.println("Fils : Test sur "+noeud2+","+noeud1+" nb croisements = "+nbCrossing2);
        }
        if(nbCrossing1 > nbCrossing2) {
          // Permutation de noeud1 avec noeud2
           permutter(v, i, j);
           nbTotal += nbCrossing2;
           test = true;
        }
        else nbTotal += nbCrossing1;
        j += 1;
      } // Fin while j
      i += 1;
    }// Fin while i
    return nbTotal;
  }

  /**
   * Permutter les noeuds aux positions i et j dans v
   */
  public void permutter(Vector v, int i, int j) {
    LatticeNodeGraph noeud1, noeud2;
    noeud1 = (LatticeNodeGraph) v.elementAt(i);
    noeud2 = (LatticeNodeGraph) v.elementAt(j);
    //System.out.println("On permute "+noeud1+" avec "+noeud2);
    v.setElementAt(noeud2, i);
    int x = noeud2.x();
    noeud2.setX(noeud1.x());
    v.setElementAt(noeud1, j);
    noeud1.setX(x);
  }

  /**
   * Nombre de croisements entre deux noeuds, si le x de noeud1 est inférieur au x de noeud2
   */
  public int nbCrossing(Vector v1, Vector v2) {
    int nbCrossing = 0;
    //Vector peres1 = peres(noeud1);
    //Vector peres2 = peres(noeud2);
    LatticeNodeGraph n1, n2; // Les noeuds de v1, v2
    for(int i=0; i<v1.size(); i++) { // Pour chaque p?re de noeud1
      n1 = (LatticeNodeGraph) v1.elementAt(i);
      for(int j=0; j<v2.size(); j++) { // Pour chaque p?re de noeud2
        n2 = (LatticeNodeGraph) v2.elementAt(j);
        if(n1.x() > n2.x()) {
          //System.out.println("Noeud "+noeud1+" pere "+pere1+">"+"Noeud "+noeud2+" pere "+pere2);
          nbCrossing += 1;
        }
      }
    }
    return nbCrossing;
  }


  /**
   * Nombre de croisements des relations incidentes d'un ensemble de noeuds
   */
 /* public int nbCrossing(Vector v) {
    int nbCrossing = 0;
    LatticeNodeGraph noeud1, noeud2;
    for(int i=0; i<v.size(); i++) { // Pour chaque p?re de noeud1
      noeud1 = (LatticeNodeGraph) v.elementAt(i);
      for(int j=i; j<v.size(); j++) { // Pour chaque p?re de noeud2
        noeud2 = (LatticeNodeGraph) v.elementAt(j);
        nbCrossing += nbCrossing(noeud1, noeud2);
      }
    }
      return nbCrossing;
  }*/


  /**
   * Ordonner selon le nombre de relations
   */
  public Vector ordonnerMax(Vector v1) {
    Vector v2 = new Vector(v1.size());
    LatticeNodeGraph max;
    while( ! v1.isEmpty()) {
      max = max(v1);
      v2.add(max);
      int index = v1.indexOf(max);
      if(index != -1) v1.removeElementAt(index);
    }
    return v2;
  }

  public LatticeNodeGraph max(Vector v1) {
    int maxNbFils = -1;
    LatticeNodeGraph max = null;
    for(int i = 0; i< v1.size(); i++) {
      LatticeNodeGraph n1 = (LatticeNodeGraph) v1.elementAt(i);
      if(n1.nbFils()>maxNbFils) {
        maxNbFils = n1.nbFils();
        max = n1;
      }
    }
    return max;
  }

  public int nbCommonFils(LatticeNodeGraph n1, LatticeNodeGraph n2) {
    Vector f1 = n1.fils();
    Vector f2 = n2.fils();
    int n = 0;
    for(int i=0; i<f1.size(); i++) {
      if(f2.indexOf(f1.elementAt(i)) != -1) n+=1;
    }
    return n;
  }

}