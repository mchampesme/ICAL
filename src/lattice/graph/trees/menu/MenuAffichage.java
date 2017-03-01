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

package lattice.graph.trees.menu;

// import java
import java.awt.Color;
import java.awt.Menu;
import java.awt.MenuItem;
import java.awt.event.ActionListener;

import lattice.graph.trees.TreeEditor;
import lattice.graph.trees.event.MenuAffichageAdapter;
import lattice.graph.trees.event.MenuColorAdapter;
import lattice.graph.utils.Resources;

/**
	* IKBS - MenuAffichage
	* Définition de la classe MenuEdition, sous classe de MenuItem
	* Classe qui implémente le Menu Edition
	* @author David Grosser
	* @date 21 Octobre 1998
	* @since ?
*/
public class MenuAffichage extends Menu {

	TreeEditor editeur;
/**
	* Différent MenuItem de la barre de Menu qui sont mis en variables d'instance pour pouvoir ?tre modifiés
*/
	public MenuItemChange flechesRel = new MenuItemChange("Afficher fl?ches F7", "Masquer fl?ches F8");
	public MenuItemChange relationForme = new MenuItemChange("Lignes droites F5", "Lignes brisées F6");
	public MenuItemChange textRelations = new MenuItemChange("Afficher texte relations", "Masquer texte relations");
	public MenuItemChange posLien = new MenuItemChange("Verticale", "Horizontale");
	public MenuItemChange affZoomViewer = new MenuItemChange("Afficher fen?tre de zoom", "Masquer fen?tre de zoom");
	public MenuItemChange affichAttributs = new MenuItemChange("Afficher", "Masquer");
	public MenuItemChange affInfo = new MenuItemChange("Afficher informations", "Masquer informations");

	public MenuAffichage(TreeEditor editeur, String nom) {
		super(nom);
		this.editeur = editeur;
		init();
	}

	protected void init() {
		affZoomViewer.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.AFF_ZOOM, editeur));
		add(affZoomViewer);
		add(affInfo);
		affInfo.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.AFF_INFO, editeur));
		addSeparator();
		MenuItem format1 = new MenuItem("Arbre simple		F1");
		add(format1);
		format1.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.FORMAT_1, editeur));
		MenuItem format2 = new MenuItem("Arbre équilibré horizontal F2");
		add(format2);
		format2.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.FORMAT_2, editeur));
		MenuItem format3 = new MenuItem("Arbre équilibré vertical 	F3");
		add(format3);
		format3.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.FORMAT_3, editeur));
		MenuItem format4 = new MenuItem("Graphe 	F4");
		add(format4);
		format4.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.FORMAT_4, editeur));
		addSeparator();
		MenuItem zoomMoins = new MenuItem("Zoom - 	F9");
		add(zoomMoins);
		zoomMoins.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.ZOOM_MOINS, editeur));
		MenuItem zoomPlus = new MenuItem("Zoom + 	F10");
		add(zoomPlus);
		zoomPlus.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.ZOOM_PLUS, editeur));

	// Définition du menu Objets, sous Menu de Affichage
		String polices[] = Resources.getToolkit().getFontList();
		//String polices[] = Toolkit.getDefaultToolkit().getFontList();
			Menu objets = new Menu("Objets");
				Menu police = createPoliceMenu(new MenuAffichageAdapter(MenuAffichageAdapter.CHANGE_POLICE_OBJ, editeur));
				objets.add(police);
				//objets.addSeparator();
				Menu style = createStyleMenu(new MenuAffichageAdapter(MenuAffichageAdapter.CHANGE_STYLE_OBJ, editeur));
				objets.add(style);
				Menu couleur = new Menu("Couleur");
					MenuColorAdapter colorTextAdapter = new MenuColorAdapter(MenuColorAdapter.TEXT_OBJET, editeur);
					Menu couleurText = createColorMenu(colorTextAdapter);
					couleurText.setLabel("Texte");
					couleur.add(couleurText);

					//Menu couleurFond = new Menu("Fond");
					MenuColorAdapter colorFondAdapter = new MenuColorAdapter(MenuColorAdapter.FOND_OBJET, editeur);
					Menu couleurFond = createColorMenu(colorFondAdapter);
					couleurFond.setLabel("Fond");
					couleur.add(couleurFond);
				objets.add(couleur);
			addSeparator();
			add(objets);

		// Définition du Menu Attributs
		Menu attributs = new Menu("Attributs");
			attributs.add(affichAttributs);
			affichAttributs.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.AFF_ATTRIB, editeur));

			attributs.addSeparator();
			Menu policeAtt = createPoliceMenu(new MenuAffichageAdapter(MenuAffichageAdapter.CHANGE_POLICE_ATT, editeur));
			attributs.add(policeAtt);
			Menu styleAtt = createStyleMenu(new MenuAffichageAdapter(MenuAffichageAdapter.CHANGE_STYLE_ATT, editeur));
			attributs.add(styleAtt);

		Menu couleurAtt = new Menu("Couleur");
				MenuColorAdapter colorTextAttAdapter = new MenuColorAdapter(MenuColorAdapter.TEXT_ATT, editeur);
				Menu couleurTextAtt = createColorMenu(colorTextAttAdapter);
				couleurTextAtt.setLabel("Texte");
				couleurAtt.add(couleurTextAtt);
				MenuColorAdapter colorFondAttAdapter = new MenuColorAdapter(MenuColorAdapter.FOND_ATT, editeur);
				Menu couleurFondAtt = createColorMenu(colorFondAttAdapter);
				couleurFondAtt.setLabel("Fond");
				couleurAtt.add(couleurFondAtt);
			attributs.add(couleurAtt);
		add(attributs);
// Fin définition du Menu Attributs
// Fin définition du Menu des objets

// Définition du Menu Relations
		Menu relations = new Menu("Relations");
			relations.add(relationForme);
			relationForme.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.CHANGE_FORMEREL, editeur));
			//relations.addSeparator();

			relations.add(flechesRel);
			flechesRel.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.CHANGE_FLECHES, editeur));

			relations.add(textRelations);
			textRelations.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.TEXT_RELATIONS, editeur));
			//relations.addSeparator();

			//posLien = new MenuItem("Liens verticaux");
			relations.add(posLien);
			posLien.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.POS_LIENS, editeur));
			relations.addSeparator();
			Menu policeRel = createPoliceMenu(new MenuAffichageAdapter(MenuAffichageAdapter.CHANGE_POLICE_REL, editeur));
			relations.add(policeRel);
			Menu styleRel = createStyleMenu(new MenuAffichageAdapter(MenuAffichageAdapter.CHANGE_STYLE_REL, editeur));
			relations.add(styleRel);
		add(relations);
// Fin définition du Menu Relations
		// Définition du menu fond
			Menu fond = new Menu("Fond");
				MenuItem motif = new MenuItem("Ouvrir image");
				motif.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.SET_IMAGE, editeur));
				fond.add(motif);
				//Menu alignement = new Menu("Alignement");
				Menu alignement = createMenuAlignement(new MenuAffichageAdapter(MenuAffichageAdapter.SET_ALIGNEMENT, editeur));
				//alignement.addActionListener(new MenuAffichageAdapter(MenuAffichageAdapter.SET_ALIGNEMENT, editeur));
				fond.add(alignement);
			add(fond);

// Définition du menu préférences de l'affichage
		//addSeparator();
	}

	protected Menu createColorMenu(ActionListener mca) {
		Menu colorMenu = new Menu ("Couleur");
		String labelColorTable[] = {"Noir", "Bleu", "Cyan", "Gris", "Vert", "Magenta", "Orange", "Rose", "Blanc", "Jaune"};
		Color colorTable[] = {Color.black, Color.blue, Color.cyan, Color.gray, Color.green, Color.magenta, Color.orange, Color.pink, Color.white, Color.yellow};
		for(int i=0; i<10; i++) {
			MenuItemColor menuItem = new MenuItemColor(labelColorTable[i], colorTable[i]);
			colorMenu.add(menuItem);
			menuItem.addActionListener(mca);
		}
		return colorMenu;
	}

	protected Menu createPoliceMenu(ActionListener listener) {
		String polices[] = Resources.getToolkit().getFontList();
		Menu police = new Menu("Polices");
		for(int i=0; i<polices.length; i++) {
			MenuItem m = new MenuItem(polices[i]);
			m.addActionListener(listener);
			police.add(m);
		}
		return police;
	}

	protected Menu createMenuAlignement(ActionListener listener) {
		String align[] = {"Aucun", "Centrer", "Gauche", "Bas", "Motif", "Adapter", "Grille"};
		Menu malign = new Menu("Alignement");
		for(int i=0; i<align.length; i++) {
			MenuItem m = new MenuItem(align[i]);
			m.addActionListener(listener);
			malign.add(m);
		}
		return malign;
	}

	protected Menu createStyleMenu(ActionListener listener) {
		String style[] = {"Normal", "Italique", "Gras", "Gras italique"};
		Menu mStyle = new Menu("Styles");
			for(int i=0; i<style.length; i++) {
				MenuItem m = new MenuItem(style[i]);
				m.addActionListener(listener);
				mStyle.add(m);
			}
		return mStyle;
	}

}