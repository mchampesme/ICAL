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

package lattice.graph.trees;import java.awt.Color;import java.util.Observable;import java.util.Observer;public class Attribut extends Object implements Observer, Cloneable, Selectable {	// Variables de classes	static protected int num = 0;	// Variables d'instance	protected boolean selected = false;	protected boolean clicked = false;	protected boolean cible = false;	protected String label;	protected Noeud pere;/* Constructeurs */	public Attribut(Noeud unNoeud) {		super();		this.pere = unNoeud;		num++;		this.label = new String("attribut n°"+num);	}	public Attribut(Noeud unNoeud, String libelle) {		super();		this.label = libelle;		this.pere = unNoeud;		num++;	}	// Méthodes d'acc?s/************************ Interface Selectable ************************/	public boolean getSelected() {		return selected;	}	public void setSelected(boolean selected) {		this.selected = selected;	}	public boolean getClicked() {		return clicked;	}	public void setClicked(boolean clicked) {		this.clicked = clicked;	}// fin interface selectable	public boolean getCible() {		return cible;	}	public void setCible(boolean cible) {		this.cible = cible;	}	public String getLabel() {return label;}	public void setLabel(String libelle) {		this.label = libelle;	}	public void setPere(Noeud pere) {		this.pere = pere;	}	public Noeud getPere() {		return pere;	}	public Color getColorType() {		return Color.black;	}	public void initNewPere(Noeud pere) {setPere(pere);}/**	* s'il y a des illustrations associées*/	public boolean isThereIllustration() {		return false;	}/**	* Par défaut, cette méthode retourne 0. Elle doit ?tre surchargée pour retourner autre chose que 0*/	public int nbIllustration() {		return 0;	}/**	* Implémente Observer*/	public void update(Observable o, Object args) {		if(pere != null) pere.update(o, args);	}/**	* Implémente Cloneable*/	public Object clone() {		//System.out.println("clone de Attribut");		Attribut newAtt = new Attribut(this.pere);		newAtt.label = this.label;		return newAtt;	}/**	* Retourne l'info associée*/	public String getInfo() {		return getLabel();	}}// fin classe Attribut