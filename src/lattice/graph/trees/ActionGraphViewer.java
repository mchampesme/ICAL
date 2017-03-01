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

package lattice.graph.trees;// import javaimport java.awt.Color;import java.awt.Cursor;import java.awt.Dimension;import java.awt.Rectangle;import java.awt.event.MouseEvent;import java.awt.event.MouseMotionListener;import java.util.Vector;import lattice.graph.dialog.DialogListener;import lattice.graph.dialog.ValidationDialog;import lattice.graph.trees.event.ActionGraphViewerAdapter;import lattice.graph.trees.event.FormatKeyListener;import lattice.graph.zoom.ZoomInterface;/** * IKBS - IREMIA, Universit� de la R�union * D�finition de ActionGraphViewer, sous classe de GraphViewer * Impl�mente les comportements d'un canvas dynamique (PopUpMenu, d�placements, repositionnement, etc.) * @date 18 Juillet 1997 * @version Version v2.2 * @author David Grosser */public class ActionGraphViewer extends GraphViewer implements Runnable, MouseMotionListener, ZoomInterface, DialogListener {  public static int NORMAL = 1; // vitesse de d�filement normale  public static int RAPIDE = 2; // vitesse de d�filement rapide  public static int TRES_RAPIDE = 3; // vitesse de d�filement tr?s rapide// Pour la gestion de l'animation  public static boolean anim = true;  public static double FLUIDITE = 0.05; //  = 1 : Un rafraichissement par d�calage d'un pixel  //  = 0.5 : Un rafraichissement par d�calage de deux pixel, etc  public static int MAX_ITER = 20;  public static int TIME_SLEEP = 5;  protected int xDepart, yDepart;  protected Thread monThread; // Le Thread qui se charge de g�rer le calcul  //protected boolean changedAff = false; // Variable qui g?re le fait que le d�placement � d�j� �t� effectu�// Fin gestion de l'animation  protected boolean edition = true; // On n'est pas en mode edition  // Les popupMenu  protected IkbsPopupMenu canvasPopUp;	// Menu contextuel du fond du canvas  protected ComponentPopUp componentPopUp;// Menu contextuel des objets  protected AttributPopUp attributPopUp;	// Menu contextuel des attributs  protected int index;					// L'index du noeud selectionn�  protected Selectable[] selected = new Selectable[10];			// L'attribut ou l'objet s�lectionn�  protected int vitesse = RAPIDE;  protected boolean attributClic = false;  protected boolean attributDrag = false;  protected boolean copyMode = false;  /**   * Initialisation du ActionGraphViewer   * Mise en place des Listeners   */  public void init() {    super.init();    //System.out.println("Init de ActionGraphViewer");    //setBackground(Color.lightGray);    addKeyListener(new FormatKeyListener(this));    //addMouseMotionListener(this);    addMouseListener(new ActionGraphViewerAdapter(this));  }  /**   * Surcharge de la m�thode getPreferredSize() de java.awt.Component   * Permet de s'adapter automatiquement lors d'un redimensionnement   */  public Dimension getPreferredSize() {    return getParent().getSize();  }  /**   * R�cup�rer le PopUp des attributs   */  public AttributPopUp getAttributPopUp() {    return attributPopUp;  }  /**   * R�cup�rer le PopUp des composants   */  public ComponentPopUp getComponentPopUp() {    return componentPopUp;  }  /**   * R�cup�rer le PopUp du canvas   */  public IkbsPopupMenu getCanvasPopUp() {    return canvasPopUp;  }  /**   * return true si le canvas est en mode �dition   * en mode �dition, toute action est possible sir le canvas (d�placer les objets, etc.)   */  public boolean getEdition() {    return edition;  }  /**   * affecte la variable edition   */  public void setEdition(boolean b) {    edition = b;  }  /**   * Positionne le mode copy ou nom   */  public void setCopyMode(boolean b) {    copyMode = b;  }  /**   * affecter l'index du noeud s�lectionn�   */  public void setIndex(int index) {    this.index = index;  }  /**   *	affecter l'attribut s�lectionn�   */  public void setAttributSelect(Attribut att) {    this.selected[0] = att;  }  /**   * Retourne le nom de la fen?tre (String) qui est d�pendant de la variable �dition   */  public String nomEdition() {    String s;    if(edition) s = "Editeur de mod?le : ";    else s = "Visualiseur de mod?le : ";    return s;  }  /**   * Affecter la racine de l'arbre   */  public void affecteRacine(Noeud n) {    if ((noeudRacine != null) && (noeudRacine == n)) {      setRacine(null) ;    }    else setRacine(n) ;    refreshNoeud(n);  }  /**   * Affectation de la cible. La cible peut ?tre par exemple la cible du moteur d'induction   * Surcharg�e par les sous-classes   */  public void setCible(Attribut a) {  }  /**   * pour G�rer les �venements sur les attributs   */  public boolean isAttribute(int index, int x, int y) {    return noeuds(index).rect2().contains(x, y);  }  public Attribut attributAt(int index, int x, int y) {    return noeuds(index).dansAttributs(x, y);  }  public void setAttributCible(Attribut a) {    setCible(a);    repaint();  }  public void setAttributCible() {    if(selected[0] != null) setAttributCible((Attribut) selected[0]);  }  public void editer(Attribut a, int index) {    editer(a, noeuds(index));  }  public void editerAttribut() {    editer((Attribut) selected[0], index);  }  /**   *	Pour cr�er une relation sur le noeud � l'index   */  public void createRelation(int index) {    if(getEdition()) {      relationMode = true ;      setNoeudSelect(noeuds(index));    }  }  /**   *	Pour cr�er un noeud lorsque l'on clic sur le canvas   *	x, y : la position du clic   */  public void createNode(int x, int y) {    if(getEdition()) {      Noeud n = creerNoeud(x, y);      ajouterNoeud(n);      refreshNoeud(n);    }  }  /**   *	Pour cr�er un noeud lorsque l'on clic sur le canvas   *	a la position du dernier clic   */  public void createNode() {    if(getEdition()) createNode(pos.x, pos.y);  }  /**   *	Pour cr�er un noeud lorsque l'on clic sur le canvas   *	x, y : la position du clic   */  public NodeGraph createNode(String nom, int x, int y) {    if(getEdition()) {      Noeud n = creerNoeud(nom, x, y);      ajouterNoeud(n);      refreshNoeud(n);      return (NodeGraph) n;    }    return null;  }  /**   * Pour cr�er un nouvel attribut (Pomme sur un attribut)   * Rattach� au noeud n   */  public Attribut createAttribute(Noeud n) {    if(getEdition()) {      //System.out.println("createAttribute de ActionGraphViewer");      return(n.createAttribute());    }    return null;  }  /**   * Pour cr�er un nouvel attribut (Pomme sur un attribut)   * � partir de l'index du noeud   */  public Attribut createAttribute(int i) {    return createAttribute(noeuds(i));  }  /**   * Pour s�lectionner un Node   */  public void selectNode(int index) {    selectNode(noeuds(index));  /*if(selected != null) selected.setSelected(false);  selected = (Selectable) noeudSelect;  noeudSelect.setSelected(true);  repaint();*/  }  /**   * s�lection d'un noeud   */  public void selectNode(Noeud unNoeud) {    //doSelected((Selectable) unNoeud);    setNoeudSelect(unNoeud);    putLastPosition(noeudSelect);    refreshNoeud(noeudSelect);    noeudClicked(noeudSelect);  }  public void doSelected(Selectable s) {    if(selected[0] != s) {      if(selected[0] != null) selected[0].setSelected(false);      if(s != null) s.setSelected(true);      selected[0] = s;    }  }  /**   * Permet de modifier les couleurs pour mettre en relief le noeud s�lectionn�   *//*	public synchronized void updateColorNDG(Noeud ndgold, Noeud ndg) {  if(ndgold != null) ndgold.initColor();  if(ndg != null) {    ndg.setLabelColor(Color.white);// Le text s'affiche en blanc    ndg.setBgColor(new Color(180, 10, 10));// Le fond devient rouge  } }	*//** * Selection d'un noeud sans l'affecter en temps que noeud s�lectionn� */  public void selectNode2(int index) {    if(selected[0] != null) selected[0].setSelected(false);    select = true;    noeuds(index).setSelected(true);    setNoeudSelect(noeuds(index));    putLastPosition(noeudSelect);    refreshNoeud(noeudSelect);    noeudClicked(noeudSelect);  /*if(selected != null) selected.setSelected(false);  selected = (Selectable) noeudSelect;  noeudSelect.setSelected(true);  repaint();*/  }/*	public void selectNode(int index) {  select = true;  noeuds(index).setSelected(true);  noeudSelect = noeuds(index);  putLastPosition(noeudSelect);  refreshNoeud(noeudSelect);  noeudClicked(noeudSelect); }*/ /**  *	Pour d�placer le sous arbre de racine le noeud � l'index  */  public void moveTree(int index) {moveTree(noeuds(index));}  public void moveTree(Noeud n) {    if (edition) {      select = true;      shiftPressed = true;      n.setSelected(true);      setNoeudSelect(n);      //rect = setRect(noeudSelect);      refreshNoeud(noeudSelect);    }  }  /**   * Pour �diter un noeud   */  public void editNode() {editNode(index);}  public void editNode(int index) {    selectNode(index);    editer(noeudSelect);  }  public void eraseNode(int index) {    //System.out.println("erase node a l'index "+index);    if (getEdition()) {      //effacerRelations(noeuds(index));      effacerNoeud(index);      rect = null;      repaint();    }    else System.out.println("Impossible d'effacer en mode visualisation");  }  public void eraseNode() {    eraseNode(index);  }  /**   * Effacer l'attribut s�lectionn�   */  public void eraseAttribut() {    ((Attribut) selected[0]).getPere().removeAttribut(((Attribut) selected[0]).getLabel());  }  /**   *	Effacer l'arbre de racine le noeud � l'index   */  public void eraseTree(int index) {    if (getEdition()) {      effacerNoeudsRec(noeuds(index));      rect = null;      repaint();    }  }  public void eraseTree() {    eraseTree(index);  }  public void eraseAll() {    noeuds = new Vector();    //relations = new Vector();    rect = null;    formatter = null;    repaint();  }  /**   *	On affecte la racine au noeud index   */  public void rootOnNode(int index) {    if (getEdition()) {      affecteRacine(noeuds(index));    }  }  public void rootOnNode() {    rootOnNode(index);  }  /**   * Duplication du noeud � l'index index   */  public Noeud copyNode() {    return copyNode(index);  }  /**   * Copie d'un noeud   */  public Noeud copyNode(int index) {    return copyNode(noeuds(index));  }  /**   * Afficher / masquer les attributs d'un noeud   */  public void changeAffAttributs() {    Noeud n = noeuds(index);    changeAffAttributs(n, ! n.affAttributs());  }  public void affSousArbre() {    Noeud n = noeuds(index);    demarquer();// Pour g�rer les cycles    affSousArbre(n, ! n.isFilsVisible());  }  /**   * Copie d'un noeud   */  public Noeud copyNode(Noeud n) {    if(edition) {      Noeud copy = (Noeud) n.clone();      copy.bouge(3, 3);      calculDimension(copy);      ajouterNoeud(copy);      selectNode(copy);      return copy;    }    return n;  }  /**   * Copie d'un arbre (ou sous-arbre)   */  public Noeud copyTree() {    return copyTree(index);  }  /**   * Copie d'un arbre (ou sous-arbre)   */  public Noeud copyTree(int index) {    return copyTree(noeuds(index));  }  /**   * Copie d'un arbre (r�cursive)   */  public Noeud copyTree(Noeud unNoeud) {    if(edition) {      Noeud copy = copyNode(unNoeud);      Vector fils = unNoeud.fils();      for(int i=0; i<fils.size(); i++) {        Noeud copyFils = copyTree((Noeud) fils.elementAt(i));        initRelation(new Relation(copy, copyFils));      }      selectNode(copy);      return copy;    }    return unNoeud;  }  /**   *	on passe en mode drag   */  public void dragMode() {    //rect = null;    setCursor(new Cursor(Cursor.MOVE_CURSOR));    //pos.x=x()+pos.x;    //pos.y=y()+pos.y;    drag = true;    //if(zoomCanvas != null) zoomCanvas.clearRect();  }// fin drag mode  /**   * Appel�e lorsque l'on clic sur un noeud   */  public void noeudClicked(Noeud noeudSelect) {    ((Selectable) noeudSelect).setClicked(true);    select = true;    setInfo(noeudSelect.getInfo());    repaint();  }  /**   * Appel�e lorsque l'on clic sur un attribut   */  public void attributClicked(Attribut a, Noeud noeudSelect) {  /*if(selected != null) {   selected.setSelected(false);  }  a.setSelected(true);  selected = a;*/    //doSelected(a);    a.setClicked(true);    setInfo(a.getInfo());    repaint();  }  /**   * S�lection d'un attribut   */  public void attributClicked(Attribut attribut, int index) {    attributClicked(attribut, noeuds(index));    attributClic = true;    setInfo(attribut.getInfo());    //selectNode(index);  }  public void attributMoved(int x, int y) {    attributDrag = false;    eraseNode();    int index = rechNoeud(x, y);    if((index != -1)&&(noeuds(index).find((Attribut) selected[0]) == -1)) copyAttribut(noeuds(index));    else {      ValidationDialog d = new ValidationDialog(getFrame(), "Effacer un attribut ", true, this, "Voulez-vous effacer l'attribut "+selected[0].getLabel()+" ?", "annuler", "effacer");      d.show();    }  }// impl�mente DialogListener  public void valider() {  }// impl�mente DialogListener  public void annuler() {    copyMode=false;    copyAttribut(((Attribut) selected[0]).getPere());  }  /**   * Copie de l'attribut s�lectionn� dans le noeud pass� en param?tre   */  protected void copyAttribut(Noeud n) {  /*if(n == null) System.out.println("le noeud est null");  else System.out.println("le noeud n'est pas null : "+n);*/    if(copyMode) {      Attribut newAtt = (Attribut) ((Attribut) selected[0]).clone();      //System.out.println("appel � clone de ActionGraphViewer");      newAtt.initNewPere(n);    }    else {      //System.out.println("appel � clone de ActionGraphViewer :"+copyMode);      ((Attribut) selected[0]).initNewPere(n);    }  }  /**   * Pour copier un attribut   * M�thode appel�e via le popUp   */  public void copyAttribut() {    copyMode = true;    //copyAttribut(((Attribut) selected).getPere());    //System.out.println("ancien noeud"+((Attribut) selected).getPere());    copyAttribut(((Attribut) selected[0]).getPere());    copyMode = false;  }  /**   * On d�place un attribut   */  public void deplacerAttribut(int x, int y) {    if((getEdition())&&(! attributDrag)) {      //noeudSelect = noeuds(rechNoeud(x, y));      if(copyMode) {        //selected.setSelected(false);        //Noeud n = ((Attribut) selected).getPere();        //if(n != null) refreshNoeud(n);        //doSelected(null);      }      createNode(((Attribut) selected[0]).getLabel(), x, y);      attributDrag = true;      index = rechNoeud(x, y);      selectNode2(index);      noeuds(index).setBgColor(Color.white);      noeuds(index).setLabelColor(((Attribut) selected[0]).getColorType());      if(! copyMode) eraseAttribut();      //attributSelect.getPere().removeAttribut(attributSelect.getLabel());    }  }  /**   * D�placement du canvas   */  public void deplacer2(int x, int y) {    int decX = (x - pos.x) * vitesse;    int decY = (y - pos.y) * vitesse;    setX(decX);    setY(decY);    pos.x=x;    pos.y=y;    if(zoomCanvas != null) zoomCanvas.setRect(new Rectangle(-getX(), -getY(), getSize().width, getSize().height));    repaint();  }  /**   * Lorsque l'on d�place la souris avec le doigt appuy�   */  public void mouseDragged(MouseEvent e) {    //setCursor(new Cursor(Cursor.MOVE_CURSOR));//le curseur prend la forme d'une main    int x = e.getX();    int y = e.getY();    if((attributClic)&&(((Math.abs(x-pos.x)>5))||(Math.abs(y-pos.y)>5))) {      deplacerAttribut(x, y);      attributClic = false;    }    else {      if(drag) {        deplacer2(x, y);      }      else {        if(getEdition()) if(relationMode) relationMode(x, y);        else if (select) selectMode(x, y);      }    }  }  public void mouseMoved(MouseEvent e) {  }  protected void relationMode(int x, int y) {    if(getEdition()) {      if (relationSelect == null) { // On cree un objet relationSelect (relation non terminee)        relationSelect = new RelationSelect(noeudSelect, x, y) ;        initRelation(relationSelect);      }      else {        setRect(relationSelect.rect()) ;        relationSelect.setPos(x, y) ;        addRect(relationSelect.rect());        repaint();      }    }  }  /**   * On passe en mode d�placement d'un noeud   */  protected void selectMode(int x, int y) {    //if(getEdition()&&(((Math.abs(x-pos.x)>5))||(Math.abs(y-pos.y)>5))) {    //System.out.println("SelectMode");    if(getEdition()) {      //int dx = x - noeudSelect.x();      //int dy = y - noeudSelect.y();      int dx = x - pos.x;      int dy = y - pos.y;      pos.x += dx;      pos.y += dy;      if(shiftPressed) {// on deplace tout le sous arbre        bougeNoeudRec(noeudSelect, dx, dy);        repaint();      }// fin if shiftpressed      else bougeNoeud(noeudSelect, dx, dy);    }  } // fin mouseDraging  /**   * Lorsque l'on a cliqu� et que l'on relache le bouton   */  public boolean mouseUp(int x, int y) {    attributClic = false;    shiftPressed = false;    if(drag) {// Lorsque l'on scroll l'arbre tout entier      drag = false;      pos.x=0;      pos.y=0;      setX(0);      setY(0);    }// fin if drag    if (select) {// Lorsque l'on s�lectionne et qu'on d�place un noeud      ((Selectable) noeudSelect).setClicked(false);      refreshNoeud(noeudSelect);      //noeudSelect = null;      select = false;      //if(zoomCanvas != null) zoomCanvas.refresh();    }    else {      if((selected[0] != null)&&(selected[0] instanceof Attribut)) {// C'est un attribut        selected[0].setClicked(false);        Noeud n = ((Attribut) selected[0]).getPere();        if(n != null) refreshNoeud(n);      }    }    if(relationMode) {// Lorsque l'on cr�e une relation      int index = rechNoeud(x, y);      if(index != -1) {// Le noeud a �t� trouv�        if(noeudSelect == noeuds(index)) {          noeudSelect.createAttribute();          //repaint();        }        else {          Relation r = new Relation(noeudSelect, noeuds(index));          initRelation(r);          refreshNoeud(noeudSelect);        }      }      else {// Le noeud n'a pas �t� trouv�        //relationSelect = null ;        repaint();        //if(zoomCanvas != null) zoomCanvas.refresh();      }// fin else    }	// fin if    if(attributDrag) attributMoved(x, y);    copyMode = false;    relationMode = false;    //noeudSelect = null ;    relationSelect = null ;    //return super.mouseUp(evt, x, y);    setCursor(new Cursor(Cursor.DEFAULT_CURSOR));//le curseur prend la forme d'une main    return false;  } // fin mouseUp  /**   * Gestion du recentrage dynamique   * (x, y) : les coordonn�es du point � recentrer   */  public void recentreAuto(int x, int y) {    //changedAff = false;    int xFinal = getSize().width/2 - xDepart; // Centre en x de la fen?tre    int yFinal = getSize().height/2 - yDepart; // Centre en y de la fen?tre    deplacerAuto(xFinal, yFinal);    //monThread.suspend();  }  /**   * d�placement du canvas de mani?re � amener le point du canvas cliqu� aux coordonn�es (x, y)   */  public void deplacerAuto(int x, int y) {    double decX, decY;    double accumX = 0.0;    double accumY = 0.0;    int xFinal = x;// - pos.x;    int yFinal = y;// - pos.y;    //System.out.println("xFinal = "+xFinal+", yFinal = "+yFinal);    double distance = Math.sqrt((double) (xFinal*xFinal+yFinal*yFinal));    int nb_iter = (int) (distance * FLUIDITE);    if(nb_iter > MAX_ITER) nb_iter = MAX_ITER;    //int degreWait = nb_iter/4;    if(nb_iter == 0) repaint();    else      for(int i = nb_iter; i>0; i--) {    decX = (((double) xFinal)/((double) nb_iter)); // D�calage relatif en x � affecter au panel pour arriver � la position x    decY = (((double) yFinal)/((double) nb_iter)); // D�calage relatif en y � affecter au panel pour arriver � la position y    //waitTime(i, nb_iter);    waitTime(i, nb_iter);    accumX += decX - (int) decX;    accumY += decY - (int) decY;    if(accumX >= 1.0) {accumX -= 1.0; decX += 1.0;}    if(accumX <= -1.0) {accumX += 1.0; decX -= 1.0;}    if(accumY >= 1.0) {accumY -= 1.0; decY += 1.0;}    if(accumY <= -1.0) {accumY += 1.0; decY -= 1.0;}    while((getX()!=0)||(getY()!=0)) {try{Thread.sleep(TIME_SLEEP);}catch(Exception e){}}    setX(((int) decX));    setY(((int) decY));    if(zoomCanvas != null) zoomCanvas.setRect(new Rectangle(-getX(), -getY(), getSize().width, getSize().height));    repaint();      }  }  public void setBounds(int x, int y, int w, int h) {//public boolean setBound(int x, int y, int w, int h) {    //System.out.println("SetBounds");    super.setBounds(x, y, w, h);    if(zoomCanvas != null) {      //zoomCanvas.setRect(new Rectangle(-getX(), -getY(), getSize().width, getSize().height));      //zoomCanvas.repaint();      zoomCanvas.setRect(new Rectangle(-getX(), -getY(), w, h));      zoomCanvas.repaint();    }  }  public void waitTime(int i, int nb_iter) {    try {      if(i<(nb_iter/4)) Thread.sleep(TIME_SLEEP + (nb_iter/i*4));      else {        if(i>(3*nb_iter/4)) Thread.sleep(TIME_SLEEP + (nb_iter/(nb_iter-i)*4));        //else monThread.sleep(TIME_SLEEP);      }      } catch (Exception exp) {}  }  /**   * Permet de recentrer le canvas au coordonn�es du noeud   */  public void recentre(Noeud unNoeud) {    doSelected((Selectable) unNoeud);    super.recentre(unNoeud);  }  /**   * M�thode d�clench�e automatiquement   * Lance le Thread qui s'occupe de l'action   */  public void recentre(int x, int y) {    if(anim) {      this.xDepart = x;      this.yDepart = y;      monThread = new Thread(this);      monThread.setPriority(Thread.NORM_PRIORITY-1);      monThread.start();    }    else super.recentre(x, y);  }  public void recentreAuto() {    recentreAuto(xDepart, yDepart);  }  public void run() {    recentreAuto(xDepart, yDepart);  }} // fin classe ActionGraphViewer