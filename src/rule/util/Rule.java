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

package rule.util;

/** ********************************************************************************* */
/* Cette classe permet de d�crire les caract�ristiques des r�gles d'association. */
/* Celles-ci sont de la forme: */
/* ant�c�dent --> consequence (support, confiance) */
/** ********************************************************************************* */

import java.util.Iterator;
import java.util.SortedSet;

import lattice.alpha.util.BGIntent;
import lattice.alpha.util.Couple;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;

public class Rule extends Couple<Intent, Intent> {

	// VARIABLES D'INSTANCE

	private double support = 1.0; // Support de la r�gle
	private double confiance = 1.0; // Confiance de la r�gle

	// CONSTRUCTEUR

	public Rule(Intent antecedent, Intent consequence, double support,
			double confiance) {
		super(antecedent, consequence);
		this.support = support;
		this.confiance = confiance;
	}

	public Rule(Intent antecedent, Intent consequence) {
		super(antecedent, consequence);
	}

	public Rule(Itemset antecedent, Intent consequence, double support,
			double confiance) {
		super(antecedent.getItems(), consequence);
		this.support = support;
		this.confiance = confiance;
	}

	// METHODES D'INSTANCE

	// Confiance

	public double getConfiance() {
		return this.confiance;
	}

	// Support

	public double getSupport() {
		return this.support;
	}

	// Ant�c�dent

	public Intent getAntecedent() {
		return first();
	}

	// Cons�quence

	public Intent getConsequence() {
		return second();
	}

	public String toString() {
		String s = new String();
		Intent antecedent = getAntecedent();
		Iterator<FormalAttribute> it2 = antecedent.iterator();
		Intent consequence = getConsequence();
		Iterator<FormalAttribute> it3 = consequence.iterator();

		while (it2.hasNext()) {

			// Enregistrement de l'ant�c�dent de la r?gle
			String itemCourantant = it2.next().toString();
			s += itemCourantant += " ";
		}

		s += " --> ";
		while (it3.hasNext()) {

			// Enregistrement de la cons�quence de la r�gle
			String itemCourantcons = it3.next().toString();
			s += itemCourantcons + " ";
		}
		s += "\t\t";
		// Enregistrement du support de la r?gle
		s += "(S = ";
		String sup = Double
				.toString(((double) ((int) (getSupport() * 100.0))) / 100.0);
		s += sup;
		s += "% ; ";

		// s += "<confiance>";
		s += "C = ";

		// Enregistrement de la confiance de la r?gle
		String c = Double
				.toString(((double) ((int) (getConfiance() * 100.0))) / 100.0);
		s += c;
		s += ")";
		return s;
	}
}