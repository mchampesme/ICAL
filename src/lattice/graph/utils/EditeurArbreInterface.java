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

import lattice.graph.trees.ActionGraphViewer;

/**
	* IKBS v2.9
	* Interface pour les éditeurs qui intègre un PanelButtonArbre
	* @author David Grosser
*/

public interface EditeurArbreInterface {

/**
	* retourne l' ActionGraphViewer contenu par l'éditeur qui implémente cette interface
*/
	public abstract ActionGraphViewer getCanvas();

/**
	* Affiche ou masque le zoomCanvas
*/
	public abstract void changeAffZoomViewer();

/**
	* change le mode (édition ou visualisation)
*/
	public abstract void changeMode();

/**
	* Affiche ou masque les attributs
*/
	public abstract void affAttributs();

/**
	* Charger en local
*/
	public abstract void loadLocal();

/**
	* Charger à distance
*/
	public abstract void loadDistant();

/**
	* Sauver en local
*/
	public abstract void sauverLocal();

/**
	* Afficher la page Web associée
*/
	public abstract void showDocument();

/**
	* Doit etre implementée par les editeurs qui intègrent un panel
	* pour mettre a jour le bouton d'affichage des attributs
*/
	public abstract void affAttributs2();

/**
	* Doit etre implementée par les editeurs qui intègrent un panel
	* pour mettre a jour le bouton d'affichage du mode edition/visualisation
*/
	public abstract void changeMode2();

/**
	* Pour mettre a jour le bouton d'affichage/masquage de la fenetre de zoom
*/
	public void changeAffZoomViewer2();

/**
	* Permet de changer de langue
*/
	public void changeLangue(int langue);

}