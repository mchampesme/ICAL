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

package rule.util;/**	* RuleSet : Ensemble de r?gles	* Permet de gérer un ensemble de r?gles exactes ou approximatives	* G?re notament l'affichage	* @author David Grosser	* @date 28 Mai 2003*/import java.util.Vector;// Vérifier que lorsqu'on ajoute une r?gle elle n'existe pas déjà dans l'ensemblepublic class RuleSet extends Object {		protected Vector ruleSet;		// constructeur		public RuleSet() {		ruleSet = new Vector();	}		public RuleSet(Vector v) {		ruleSet = v;	}/**	* Acc?s au vecteur de r?gles*/	public Vector getRuleSet() {		return ruleSet;	}/**	* Modification de la base de r?gle*/	public void setRuleSet(Vector v) {		ruleSet = v;	}		public void add(Rule r) {		//if(! ruleSet.contains(r))		if(! contains(r)) ruleSet.add(r);	}		public boolean contains(Rule r) {		for(int i=0; i<ruleSet.size(); i++) {			//if(((Regle) ruleSet.get(i)).equals(r)			if(r.equals((Rule) ruleSet.get(i))) return true;		}		return false;	}		public Rule get(int i) {		return (Rule) ruleSet.get(i);	}		public int size() {		return ruleSet.size();	}		public String toString() {		String result = new String();		for(int i = 0; i<ruleSet.size() ; i++) {			Rule r = (Rule) ruleSet.get(i);			result += "R"+i+" : "+r.toString()+"\n";		}		return result;	}		}