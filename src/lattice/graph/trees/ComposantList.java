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

package lattice.graph.trees;// import javaimport java.util.Vector;/**	* IKBS tools - Package graphique pour la gestion d'arbres et de graphes	* Définition de la classe ComposantList, sous classe de Composant	* @author David Grosser	* @date Septembre 1997	* @copyright IREMIA, Université de la Réunion	* @version 2.7	* @since 4 avril 2000*/public abstract class ComposantList extends Composant {// Variables de classes	static int num = 0;// Variables d'instances	Vector liste ;  // La liste des objets	public ComposantList() {		super();		num++;		init();	}	public ComposantList(Vector uneListe) {		super();		num++;		liste = uneListe;		init();	}// Initialisation	protected void init() {		liste = new Vector();	}// Méthodes d'acc?s/**	* Ajouter un objet à la liste*/	public void add(Object objet) {		liste.addElement(objet);	}// fin add	// Eliminer un objet de la liste	public void remove(Object objet) {		liste.removeElement(objet);	}// fin remove	public int nbElement() {		return liste.size();	}}