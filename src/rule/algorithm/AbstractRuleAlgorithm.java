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

package rule.algorithm;// import javaimport java.util.HashSet;
import java.util.Set;

import lattice.gui.tooltask.AbstractJob;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLattice;
import rule.util.Rule;
/**	* Projet Galicia	* Classe abstraite pour la factorisation des m�thodes communes aux diff�rents	* algorithmes de g�n�ration de r?gles d'association	* @author D. Grosser	* @date 29 mai 2003*/public abstract class AbstractRuleAlgorithm extends AbstractJob {		private StringBuffer stringResult = new StringBuffer(); // pour stoquer des r�sultats	private MatrixBinaryRelationBuilder binRel;  // La relation binaire a traiter	private CompleteConceptLattice lattice; // Le treillis support des r?gles	private double minConfiance = 0.5 ; // confiance minimale	private double minSupport = 0.3; // support minimale	private Set<Rule> ruleSet = new HashSet<Rule>(); // Ensemble de r?gles produites// Constructeurs	public AbstractRuleAlgorithm(MatrixBinaryRelationBuilder binRel, double minConfiance, double minSupport) {		this.binRel = binRel;		this.minSupport = minSupport;		this.minConfiance = minConfiance;		}		public AbstractRuleAlgorithm(CompleteConceptLattice lattice, double minConfiance, double minSupport) {		this.lattice = lattice;		this.minSupport = minSupport;		this.minConfiance = minConfiance;		}/**	* Retourne la confiance minimale*/	public double getMinConfiance() {		return minConfiance;	}/**	* Retourne le support minimal*/	public double getMinSupport() {		return minSupport;	}/**	* retourne la base g�n�r�e sous forme de Vecteur*/	public Set<Rule> getBase() {		return ruleSet;	} 		public MatrixBinaryRelationBuilder getBinaryRelation() {
		return binRel;
	}
	/**	* retourne le nombre de r?gles*/	public int size() {		return ruleSet.size();	}	public void doAlgorithm() {		if(binRel != null) {			stringResult.append("Running "+getDescription()+" on the binary relation \""+binRel.getName()+"\""+"\n");			stringResult.append("Min Confiance = "+minConfiance+" ; Min Support = "+minSupport+" ; Nb Objects = "+binRel.getObjectsNumber()+"\n"); 		}		else {			stringResult.append("Running "+getDescription()+"\n");			stringResult.append("Min Confiance = "+minConfiance+" ; Min Support = "+minSupport+"\n");		}	}	
	public StringBuffer getStringResult() {
		return stringResult;
	}
		public String getResultat(){		return stringResult.toString();	}

	/**
	 * @return the lattice
	 */
	public CompleteConceptLattice getLattice() {
		return lattice;
	}}