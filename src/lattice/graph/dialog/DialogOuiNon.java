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

package lattice.graph.dialog;// import javaimport java.awt.BorderLayout;import java.awt.Dialog;import java.awt.FlowLayout;import java.awt.Frame;import java.awt.Label;import java.awt.Panel;import java.awt.event.ActionEvent;import lattice.graph.utils.ButtonChoix;import lattice.graph.utils.ChoixComponent;import lattice.graph.utils.InfoListener;public class DialogOuiNon extends Dialog implements InfoListener {// Variables de classe pour les actions	protected static final int ANNULER 	= 0;	protected static final int VALIDER 	= 1;// Le label du bouton gauche	protected String texte;// Le label du bouton gauche	protected String bGauche = new String("Annuler");// Le label du bouton droit	protected String bDroit = new String("Valider");// Le recepteur des messages valider et annuler	protected DialogListener dl;	public DialogOuiNon(Frame owner, String title, boolean modal) {		super(owner, title, modal);		if(owner instanceof DialogListener) dl = (DialogListener) owner;		init();		pack();	}	public DialogOuiNon(Frame owner, String title, boolean modal, DialogListener dl, String gauche, String droit) {		super(owner, title, modal);		this.dl = dl;		this.bGauche = gauche;// Le bouton gauche		this.bDroit = droit;		init();		pack();	}/**	* Constructeur avec 2 boutons : gauche, droit et une ligne de texte*/	public DialogOuiNon(Frame owner, String title, boolean modal, DialogListener dl, String s, String gauche, String droit) {		super(owner, title, modal);		this.texte = s;		this.dl = dl;		this.bGauche = gauche;// Le bouton gauche		this.bDroit = droit;		init();		pack();	}	public void init() {		setLayout(new BorderLayout());		if(texte != null) add(BorderLayout.NORTH, initTexte());		add(BorderLayout.CENTER, initPButton());	}// Initialisation de la chaine d'info	public Panel initTexte() {		Panel pTexte = new Panel();		pTexte.add(new Label(texte));		return pTexte;	}/**	* Initialisation du panel des boutons*/	protected Panel initPButton() {		Panel pButton = new Panel();		pButton.setLayout(new FlowLayout());// Initialisation des boutons valider et Cancel		ButtonChoix cancel = new ButtonChoix(bGauche, this, ANNULER);		cancel.setInfo("Annuler les modifications et fermer la fen?tre");		pButton.add(cancel);		ButtonChoix ok = new ButtonChoix(bDroit, this, VALIDER);		ok.setInfo("Valider les modifications");		pButton.add(ok);		return pButton;	} // fin init initPButton	public void setInfo(String info){	}	public void removeInfo() {	}// Validation ou annulation des modifications	public void actionPerformed(ActionEvent e) {		switch(((ChoixComponent) e.getSource()).getChoix()) {			case VALIDER: valider(); dispose(); break;			case ANNULER: annuler(); dispose(); break;			default: break;		}	}	public void valider() {		if(dl != null) dl.valider();	}	public void annuler() {		if(dl != null) dl.annuler();	}}