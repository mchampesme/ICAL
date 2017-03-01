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

// import java.awt
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Point;
import java.awt.Rectangle;
import java.awt.event.MouseEvent;
import java.util.Iterator;
import java.util.Vector;

import lattice.graph.trees.ActionGraphViewer;
import lattice.graph.trees.NodeGraph;
import lattice.graph.trees.Noeud;
import lattice.graph.trees.Selectable;
import lattice.gui.graph.magneto.Magnetable;
import lattice.gui.graph.magneto.Magneto;
import lattice.gui.graph.threeD.Lattice3D;
import lattice.util.concept.Concept;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.Node;
/**
 * <p>Titre : Lattice</p>
 * <p>Description : Manipulation des treillis</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : Université de Montréal</p>
 * @author David Grosser
 * @version 1.0
 */

public class LatticeGraphViewer extends ActionGraphViewer {

  public static final int FORMATTER_HB_LATTICE  = 6; // Voir définitions dans GraphViewer
  public static final int FORMATTER_HB_LATTICE2 = 7; // Méthode de formattage verticale, en fonction du rectangle englobant
  public static final int FORMATTER_HB_LATTICE3 = 8; // Méthode de formattage verticale, en fonction du rectangle englobant

  protected Node<Concept> top; // Seule la référence sur le top du treillis est nécessaire
  public Magneto magneto;

  public boolean threeD = false;
  public Lattice3D l3D;

// Constructeur sans le top du treillis en param?tre
  public LatticeGraphViewer() {
  }

// Constructeur avec le top du treillis
/*  public LatticeGraphViewer(Node top) {
    this();
    initLatticeGraphViewer(top);
  }*/

  /**
   * Initialisation des param?tres généraux
   */
  public void init() {
    setX(0);
    setY(0);
    setZoom(9);
    initFont(getZoom());
    vitesse = NORMAL; // Vitesse du défilement
    anim = true;
    //cl = 8;				// Contrainte de positionnement de l'arbre en largeur
    //ch = 4;				// Contrainte de positionnement de l'arbre en hauteur
    pos = new Point(0, 0);
    select = false ;			// aucun noeud selectionne
    relationMode = false ;		// on n'est pas en mode relation
    setBackground(Color.white) ;// couleur du fond blanc cassé
    noeudRacine = null ; 		// pas de noeud racine

    //formeRelation = 2;
    shiftPressed = false;
    affAttributs = true;
    //fm = posFont(zoom);		// positionnement de la fonte / zoom
    showArrow = false;			// on ne montre pas les fl?ches
    drag = false ;				// pas de mode drag de la souris
    showLabelRelation = false;
    //formeRelation = Relation.FORME_ESCALIER; // formeRelation=1 : lignes droites, formeRelation=2 : lignes brisées
    formeRelation = 1;
    setEdition(true);
    addMouseListener(new LatticeGraphViewerAdapter(this));
    //addMouseListener(new ActionGraphViewerAdapter(this));
    addMouseMotionListener(this);
    addKeyListener(new FormatKeyLatticeListener(this));
  }

  /**
   * Initialisation des caractéristiques spécifiques au LatticeGraphViewer
   */
  public void initLatticeGraphViewer(Node<Concept> top) {
    this.top = top;
    setFormatter(FORMATTER_HB_LATTICE); // Méthode de formattage par défaut
    asGraphicFromTop(top); // Construction de la vue graphique
    initFormatterHBLattice(false, false); // Initialisation du formatteur

    magneto = new Magneto(this); // Initialisation de magneto
    magneto.setPriority(Thread.NORM_PRIORITY-3);
    magneto.start();
    addMouseMotionListener(magneto);
  }

  public Magneto getMagneto() {
    return magneto;
  }

  public void asGraphicFromTop(Node<Concept> top) {
    LatticeToGraph ltg = new LatticeToGraph(this);
    NodeGraph topGraph = ltg.asGraphicFromTop(top);
    setRacine(topGraph);
    //formatter();
  }

  public void initRelation(NodeGraph unNoeud, NodeGraph unFils) {
    super.initRelation(new LatticeRelation((LatticeNodeGraph) unNoeud, (LatticeNodeGraph) unFils));
  }

  public LatticeNodeGraph creerNoeud(Node<Concept> n, int x, int y) {
    LatticeNodeGraph unNoeud = new LatticeNodeGraph(n, x, y);
    unNoeud.setBordered(false);
    unNoeud.setActiveNode(active);
    calculDimension(unNoeud);
    rect = null;
    return unNoeud;
  }

  public FormatterHBLattice getFormatter() {
    return (FormatterHBLattice) formatter;
  }

  /**
   * Choix de la méthode de formattage
   */
  public void setFormatter(int i) {
    posLienRelations(1);
    switch(i) {
      case FORMATTER_HB_LATTICE: initFormatterHBLattice(false, false) ; break ;
      case FORMATTER_HB_LATTICE2: initFormatterHBLattice(true, false) ; break ;
      case FORMATTER_HB_LATTICE3: initFormatterHBLattice(true, true) ; break;
    }
  }

  public void initFormatterHBLattice(boolean fitScreen, boolean optimizer) {
    if((formatter == null)||(! (formatter instanceof FormatterHBLattice))) {
       formatter = new FormatterHBLattice(noeuds, getBounds(), zoom, fitScreen); //Formattage sans fitScreen
      //formatter = new FormatterHBLattice(this, getBounds(), zoom, fitScreen);
      //posLienRelations(1);
    }
    // posLienRelations(1);
//  }
    else {
      //posLienRelations(1);
      ((FormatterHBLattice) formatter).fitScreen = fitScreen;
      ((FormatterHBLattice) formatter).optimizerOrdre = optimizer;
      ((FormatterHBLattice) formatter).zoom = zoom;
      ((FormatterHBLattice) formatter).rectParent = getBounds();
    }
    formatter();
  }

/*  public void modAff() {
    if(noeudSelect != null) {
      noeudSelect.setSelected(false); //setAffAttributs(false);
      refreshNoeud(noeudSelect);
      noeudSelect = null;
      selected[0] = null;
    }
  }*/

/**
	* Afficher/masquer la liste des intent/extent de tous les sommets
*/
	public void affAttributs(boolean aff) {
		affAttributs = aff;
		for(int i = 0 ; i<noeuds.size() ; i++) noeuds(i).setAffAttributs(aff);
		repaint();
	}

/**
	* Afficher/masquer la liste des intent/extent d'un sommet du treillis
*/
	public void changeAffAttributs(Noeud n, boolean aff) {
		n.setAffAttributs(aff);
		repaint();
	}

  public void doSelected(Selectable s) {
    super.doSelected(s);
    if(noeudSelect != null) refreshNoeud(noeudSelect);
    //stopper();
  }

  // Déplacer le sous graph de racine n
  public void moveTree(Noeud n) {
    if(! n.getSelected()) {
      select = true;
      shiftPressed = true;
      n.setSelected(true);
      setNoeudSelect(n);
    }
    else {
      select = false;
      shiftPressed = false;
      n.setSelected(false);
    }
    refreshNoeud(noeudSelect);
  }

  /**
   * Calculer la taille idéale
   */
  //public Dimension prefSize() {
  public Dimension getPreferredSize() {
    Rectangle r = dimension();
    bougeNoeudRec(noeudRacine(), r.width/2, FormatterHBLattice.DIST_FROM_TOP);
    //setX(r.width/2 - noeudRacine().x() - 15);
    //setY(FormatterHBLattice.DIST_FROM_TOP - noeudRacine().y());

    return new Dimension(r.width, r.height + (FormatterHBLattice.DIST_FROM_TOP*3));
  }

  /**
   * Permet de recentrer le canvas au coordonnées du noeud
   */
  public void recentre(Noeud unNoeud) {
    doSelected((Selectable) unNoeud);
    super.recentre(unNoeud);
  }

  /*public Node getTop() {
    return top;
  }*/

  public Vector getNiveau() {
    return getFormatter().getvNiveau();
  }

  public Vector getNiveauRelation() {
    return getFormatter().getvNiveauRelation();
  }

  public Vector getNiveau(int i) {
    return getFormatter().getNiveau(i);
  }

  public int getcLargeur(int nbElement) {
    return getFormatter().calcRel(nbElement);
  }

  public int getcHauteur() {
    //return getFormatter().ch();
    return getFormatter().getcHauteurRel();
  }

  public int getNbNiveau() {
    return getFormatter().getNbNiveau();
  }

  public void putLastPos(Magnetable n) {
    putLastPosition((Noeud) n);
  }

 /*   public void magnet() {
      if(magneto.active) magneto.stopper();
      else magneto.active = true;
    }*/

public boolean getThreeD() {
  return threeD;
}

public void setThreeD(boolean b) {
  this.threeD = b;
  if(b) initThreeDMode();
  else {
    initTwoDMode();
    repaint();
  }
}

/**
 * Réinitialisation de la coordonnée Z à 0 de tous les noeuds
 * Lorsque l'on repasse en mode 2D
 */
public void initTwoDMode() {
  Vector v = noeuds();
  zoomCanvas.setDecalX(0);
  zoomCanvas.setDecalY(0);
  LatticeNodeGraph n;
  for(Iterator i=v.iterator(); i.hasNext() ;) {
    n = ((LatticeNodeGraph) i.next());
    n.move(getSize().width/2, 0);
    n.setZ(0);
  }
  if(zoomCanvas != null) {
  zoomCanvas.clearRect();
  zoomCanvas.refresh1();
  }
}

public void initThreeDMode() {
  new Formatter3DLattice(getNiveau());
  l3D = new Lattice3D(this);
  setX(1);
  l3D.start();
  if(zoomCanvas != null) {
      zoomCanvas.clearRect();
      zoomCanvas.refresh1();
  }
}

public void mouseDragged(MouseEvent e) {
  if(! threeD) super.mouseDragged(e);
  else l3D.mouseDragged(e);
}

public void rotation(float val) {
  l3D.rotation(val);
}

  public void paint(Graphics g) {
    if(! threeD) super.paint(g);
    else {
      l3D.paint(g);
      if((zoomCanvas != null)&&(! zoomCanvas.getQualite()))
        zoomCanvas.repaint();
    }
  }
}