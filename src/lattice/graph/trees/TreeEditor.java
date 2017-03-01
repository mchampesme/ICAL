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

package lattice.graph.trees;

// import java
import java.awt.Color;
import java.awt.FileDialog;
import java.awt.Menu;
import java.awt.Panel;

import lattice.graph.trees.event.FormatKeyListener;
import lattice.graph.trees.menu.MenuAffichage;
import lattice.graph.utils.Resources;
//import lattice.graph.zoom.ZoomEditor;

/**
        * IKBS - Editeur de mod?le
        * Définition de TreeEditor, sous classe de Editeur
        * Classe générique pour toutes les éditeurs qui affiche un ActionGraphViewer
        * @version 1.1 (mod?le évenementiel awt 1.1)
        * @author David Grosser
        * @date 30 Avril 1997
        * @since 21 10 98 - Adaptation au mod?le évenementiel de AWT 1.1
*/

public abstract class TreeEditor extends Editor {
/**
        * La couleur par défaut de la fen?tre
*/
        protected Color defaultColor = Color.white;
/**
        * Le canvas intégré dans la fen?tre
*/
        protected ActionGraphViewer idc;
/**
        * Différent Menu de la barre de Menu qui sont mis en variables d'instance pour pouvoir ?tre modifiés
*/
        protected Menu editer, affichage;
        protected boolean affInfo = false;
        protected boolean formeRel = false;
        protected boolean textRel = false;
        protected boolean arrow = false;
        protected int posLien = 1;
        protected boolean affAtt = false;
        protected boolean dynamique = false;
        protected boolean editionMode = false;
        protected boolean bufferDrag = false;

/**
        * La fen?tre de Zoom du canvas (null tant que l'on n'a pas demandé explicitement de l'afficher
*/
        //protected ZoomEditor fZoom; // La fen?tre de zoom

/**
        * Pour créer un nouvel éditeur de Canvas
        * @param nom le nom de la fen?tre
*/

/**
        * Pour créer un nouvel éditeur de Canvas
*/
        public TreeEditor(String nom) {
                super(nom);
        }// fin TreeEditor(String nom)

/**
        * Initialisation de la classe TreeEditor
        * on redimensionne la fen?tre avec une taille par défaut
*/
        public void initEditor() {
                Panel p2 = new Panel();
                idc = new ActionGraphViewer();
                p2.add("Center", idc);
                add("Center", p2);
                //resize(730, 326);
                setSize(730, 326);
                addKeyListener(new FormatKeyListener(idc));
        }// fin init

/**
        * Pour accéder au canvas ActionGraphViewer
*/
        public ActionGraphViewer getCanvas() {
                return idc;
        }

/**
        * Acc?s à la variable couleur par défaut de l'éditeur
*/
        public Color getDefaultColor() {
                return defaultColor;
        }

/**
        * Acc?s à la variable couleur par défaut de l'éditeur
*/
        public void setDefaultColor(Color rvb) {
                defaultColor = rvb;
        }

/**
        * Chargement et misse à jour de l'image de fond
*/
        public void loadBackgroundPicture() {
                String nomFich = null;
                try {
                        FileDialog fd = new FileDialog(this, "Image de fond");
                        fd.show();
                        nomFich = fd.getDirectory()+fd.getFile();
                        System.out.println(nomFich);
                }catch(Exception e) {System.out.println("Pb d'acc?s aux ressources");}
                if (nomFich != null) {
                        Resources rl = new Resources(this);
                        rl.setAcces(Resources.SANS_URL);
                        try {
                                rl.init(nomFich);
                                GraphViewer.setBackgroundPicture(rl.getImage(nomFich));
                                getCanvas().setBgAlignment("Centrer");
                        }catch(Exception e) {
                                 System.out.println("Fichier image non valide : "+ nomFich);
                         }
                }
        }

/**
        * Pour fermer la fen?tre avec libération des ressources
*/
        public void dispose() {
                /*if(idc != null) idc.dispose();
                if(fZoom != null) fZoom.dispose();
                super.dispose();*/
        }

/**
        * Permet de masquer ou démasquer le zoom Canvas
*/
        public void changeAffZoomViewer() {
                /*if(fZoom != null) {
                        fZoom.dispose();
                        fZoom = null;
                        idc.setZoomViewer(null);
                }
                else {
                        fZoom = new ZoomEditor("Zoom : " + getTitle(), idc);
                        idc.setZoomViewer(fZoom.zoomViewer());
                        fZoom.setColorPanelButton(defaultColor);
                        fZoom.setLocation(getLocationOnScreen().x+getSize().width+10, getLocationOnScreen().y);
                        fZoom.show();
                        fZoom.zoomViewer().refresh1();
                        fZoom.zoomViewer().setRect(new Rectangle(0, 0, idc.getSize().width, idc.getSize().height));
                }
                if(affichage != null) ((MenuAffichage) affichage).affZoomViewer.changeLabel();*/
        }


/**
        * Doit etre surchargée par les editeurs qui implementent EditeurArbreInterface
*/
        public void changeAffZoomViewer2() {
                //changeAffZoomViewer();
        }

/**
        * Pour changer la forme des relations et modifier le label du MenuItem en conséquence
*/
        public void changeFormeRelation() {
                formeRel = ! formeRel;
                if(formeRel) idc.changeFormeRelation(Relation.FORME_DROITE);
                else idc.changeFormeRelation(Relation.FORME_ESCALIER);
                if(affichage != null) ((MenuAffichage) affichage).relationForme.changeLabel();
        }

        public void changeTextRelation() {
                textRel = !textRel;
                if(textRel) idc.activeTextRelations();
                else idc.desactiveTextRelations();
                if(affichage != null) ((MenuAffichage) affichage).textRelations.changeLabel();
        }

        public void changeAffInfo() {
                affInfo = !affInfo;
                idc.afficherInfo(affInfo);
        }

/**
        * Pour Afficher ou masquer les fl?ches des relations et modifier le label du MenuItem en conséquence
*/
        public void changeFleches() {
                arrow = ! arrow;
                idc.setShowArrow(arrow);
                if(affichage != null) ((MenuAffichage) affichage).flechesRel.changeLabel();
        }

/**
        * Pour modifier la forme des relations et modifier le label du MenuItem en conséquence
*/
        public void posLiens() {
                if(posLien == 1) posLien = 2; else posLien = 1;
                idc.posLienRelations(posLien);
                if(affichage != null) ((MenuAffichage) affichage).posLien.changeLabel();
        }


/**
        * Un éditeur d'arbre doit permettre de s'afficher
*/
        public abstract void afficher();

/**
        * Pour modifier la forme des relations et modifier le label du MenuItem en conséquence
*/
        public void affAttributs() {
                affAtt = ! affAtt;
                idc.affAttributs(affAtt);
                if(affichage != null) ((MenuAffichage) affichage).affichAttributs.changeLabel();
        }

/**
        * Methode invoquée par le menu. Peut etre surchargée pour mettre à jour le bouton d'affichage (enfoncée ou non)
*/
        public void affAttributs2() {
                affAttributs();
        }

/**
        * Pour passer du mode visualisation au mode édition	et vice versa
*/
        public void changeMode() {
                editionMode = ! editionMode;
                idc.setEdition(editionMode);
                //if(editer != null) ((MenuEdition) editer).editerModel.changeLabel();
        }

/**
        * Acc?s au mode édition/visualisation
*/
        public boolean getMode() {
                return editionMode;
        }


/**
        * Methode invoquée par le menu. Peut etre surchargée pour mettre à jour le bouton d'affichage (enfoncée ou non)
*/
        public void changeMode2() {
                changeMode();
        }

/**
        * pour afficher la fen?tre à propos
*/
/*	public void afficherAPropos() {
                EditeurImage ei = new EditeurImage("A propos d'IKBS", docBase, "Ressources/aPropos.gif");
                ei.show();
        }*/

/**
        * Pour afficher l'éditeur de préférences
*/
/*	public void affPreferences() {
                EditeurPreferences ep = new EditeurPreferences(this);
                ep.setLocation(getLocation().x+(getBounds().width/2)-(ep.getBounds().width/2), getLocation().y+(getBounds().height/2)-(ep.getBounds().height/2));
                ep.show();
        }
*/



} // fin TreeEditors