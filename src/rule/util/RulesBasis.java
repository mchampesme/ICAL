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

/*
 * Created on 2004-08-23
 * @author Manuel Aupetit
 */
package rule.util;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import lattice.alpha.util.BGIntent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import lattice.util.relation.RelationBuilder;

/**
 * A class to represent a rules basis object
 * @author Manuel Aupetit
 */
public class RulesBasis implements Cloneable {
	
	private RelationBuilder absRel = null;
	private String datasetName = null;
	private double minSupport = 0.0;
	private double maxSupport = 1.0;
	private double minConfidence = 0.0;
	private double maxConfidence = 1.0;
	private Set<Rule> rules = null;
	private Intent premiseAttributes = null;
	private Intent consequenceAttributes = null;

	
	/**
	 * Constructor using parameters
	 * @param absRel
	 * @param rules
	 * @param minSupport
	 * @param minConfidence
	 */
	public RulesBasis(RelationBuilder absRel, Set<Rule> rules,
						double minSupport, double minConfidence) {
		
		this.absRel = absRel;
		this.datasetName = null;
		this.rules = rules;
		this.minSupport = minSupport;
		this.maxSupport = 1.0;
		this.minConfidence = minConfidence;
		this.maxConfidence = 1.0;
		setPremiseAttributes();
		setConsequenceAttributes();
	}

	/**
	 * Constructor using parameters
	 * @param absRel
	 * @param datasetName
	 * @param rules
	 * @param minSupport
	 * @param minConfidence
	 */
	public RulesBasis(	RelationBuilder absRel, String datasetName, Set<Rule> rules,
						double minSupport, double minConfidence) {
		
		this.absRel = absRel;
		this.datasetName = datasetName;
		this.rules = rules;
		this.minSupport = minSupport;
		this.maxSupport = 1.0;
		this.minConfidence = minConfidence;
		this.maxConfidence = 1.0;
		setPremiseAttributes();
		setConsequenceAttributes();
	}

	/**
	 * Constructor using parameters
	 * @param absRel
	 * @param rules
	 * @param minSupport
	 * @param maxSupport
	 * @param minConfidence
	 * @param maxConfidence
	 */
	public RulesBasis(	RelationBuilder absRel, Set<Rule> rules,
						double minSupport, double maxSupport,
						double minConfidence, double maxConfidence) {

		this.absRel = absRel;
		this.datasetName = null;
		this.rules = rules;
		this.minSupport = minSupport;
		this.maxSupport = maxSupport;
		this.minConfidence = minConfidence;
		this.maxConfidence = maxConfidence;
		setPremiseAttributes();
		setConsequenceAttributes();
	}

	/**
	 * Constructor using parameters
	 * @param absRel
	 * @param datasetName
	 * @param rules
	 * @param minSupport
	 * @param maxSupport
	 * @param minConfidence
	 * @param maxConfidence
	 */
	public RulesBasis(	RelationBuilder absRel, String datasetName, Set<Rule> rules,
						double minSupport, double maxSupport,
						double minConfidence, double maxConfidence) {

		this.absRel = absRel;
		this.datasetName = datasetName;
		this.rules = rules;
		this.minSupport = minSupport;
		this.maxSupport = maxSupport;
		this.minConfidence = minConfidence;
		this.maxConfidence = maxConfidence;
		setPremiseAttributes();
		setConsequenceAttributes();
	}

	/**
	 * Constructor using parameters
	 * @param absRel
	 * @param datasetName
	 * @param rules
	 * @param premiseAttributes
	 * @param consequenceAttributes
	 * @param minSupport
	 * @param minConfidence
	 */
	public RulesBasis(	RelationBuilder absRel, String datasetName, Set<Rule> rules,
						Intent premiseAttributes, Intent consequenceAttributes,
						double minSupport, double maxSupport,
						double minConfidence, double maxConfidence) {
		this.absRel = absRel;
		this.datasetName = datasetName;
		this.rules = rules;
		this.premiseAttributes = premiseAttributes;
		this.consequenceAttributes = consequenceAttributes;
		this.minSupport = minSupport;
		this.maxSupport = maxSupport;
		this.minConfidence = minConfidence;
		this.maxConfidence = maxConfidence;
	}
	
	
	public RelationBuilder getAbstractRelation() {
		return this.absRel;
	}
	
	public String getDatasetName() {
		return this.datasetName;
	}
	
	public double getMinSupport() {
		return this.minSupport;
	}
		
	public double getMaxSupport() {
		return this.maxSupport;
	}
		
	public double getMinConfidence() {
		return this.minConfidence;
	}
	
	public double getMaxConfidence() {
		return this.maxConfidence;
	}
		
	public Set<Rule> getRules() {
		return this.rules;
	}
	
	public int getNbRules() {
		return this.rules.size();
	}
	
	public List<FormalAttribute> getAttributes() {
		return absRel.getAttributes();
	}
	
	public Intent getPremiseAttributes() {
		return this.premiseAttributes;
	}
	
	public Intent getConsequenceAttributes() {
		return this.consequenceAttributes;
	}
	
	public void setAbstractRelation(RelationBuilder absRel) {
		this.absRel = absRel;
	}
	
	public void setDatasetName(String datasetName) {
		this.datasetName = datasetName;
	}

	public void setMinSupport(double minSupport) {
		if (minSupport >= 0.0 && minSupport <= this.maxSupport) {
			this.minSupport = minSupport;
		}
	}
	
	public void setMaxSupport(double maxSupport) {
		if (maxSupport <= 1.0 && maxSupport >= this.minSupport) {
			this.maxSupport = maxSupport;
		}
	}

	public void setMinConfidence(double minConfidence) {
		if (minConfidence >= 0.0 && minConfidence <= this.maxConfidence) {
			this.minConfidence = minConfidence;
		}
	}

	public void setMaxConfidence(double maxConfidence) {
		if (maxConfidence <= 1.0 && maxConfidence >= this.minConfidence) {
			this.maxConfidence = maxConfidence;
		}
	}
	
	public void addRule(Rule rule) {
		this.rules.add(rule);
	}
	
	public void setPremiseAttributes(Intent premiseAttributes) {
		this.premiseAttributes = premiseAttributes;
	}
	
	public void setConsequenceAttributes(Intent consequenceAttributes) {
		this.consequenceAttributes = consequenceAttributes;
	}

	public void setPremiseAttributes() {
		this.premiseAttributes = new BGIntent();
		for (Rule rule : rules) {
			premiseAttributes.addAll(rule.getAntecedent());
		}
	}
	
	public void setConsequenceAttributes() {
		this.consequenceAttributes = new BGIntent();
		for (Rule rule : rules) {
			consequenceAttributes.addAll(rule.getConsequence());
		}
	}
	
	public RulesBasis filterRulesByPremise(Intent discardedAttributes) {
		Set<Rule> newRules =  new HashSet<Rule>(rules);
		Iterator<Rule> ruleIter = newRules.iterator();
		while (ruleIter.hasNext()) {
			Rule tmpRule = ruleIter.next();
			for (FormalAttribute attr : discardedAttributes) {
				if (tmpRule.getAntecedent().contains(attr)) {
					ruleIter.remove();
					break;
				}
			}
		}
		return new RulesBasis(this.absRel, newRules, this.minSupport, this.minConfidence);
	}

	public RulesBasis filterRulesByConsequence(Intent discardedAttributes) {
		Set<Rule> newRules =  new HashSet<Rule>(rules);
		Iterator<Rule> ruleIter = newRules.iterator();
		while (ruleIter.hasNext()) {
			Rule tmpRule = ruleIter.next();
			for (FormalAttribute attr : discardedAttributes) {
				if (tmpRule.getConsequence().contains(attr)) {
					ruleIter.remove();
					break;
				}
			}
		}
		return new RulesBasis(this.absRel, newRules, this.minSupport, this.minConfidence);
	}
	
	public RulesBasis filterRulesBySupport(double minSupport, double maxSupport) {
		Set<Rule> newRules =  new HashSet<Rule>(rules);
		Iterator<Rule> ruleIter = newRules.iterator();
		while (ruleIter.hasNext()) {
			Rule tmpRule = ruleIter.next();
			double support = tmpRule.getSupport();
			if (support < minSupport || support > maxSupport) {
				ruleIter.remove();
			}
		}
		return new RulesBasis(this.absRel, newRules, minSupport, maxSupport, this.minConfidence, this.maxConfidence);
	}

	public RulesBasis filterRulesByConfidence(double minConfidence, double maxConfidence) {
		Set<Rule> newRules =  new HashSet<Rule>(rules);
		Iterator<Rule> ruleIter = newRules.iterator();
		while (ruleIter.hasNext()) {
			Rule tmpRule = ruleIter.next();
			double confidence = tmpRule.getConfiance();
			if (confidence < minConfidence || confidence > maxConfidence) {
				ruleIter.remove();
			}
		}
		return new RulesBasis(this.absRel, newRules, this.minSupport, this.maxSupport, minConfidence, maxConfidence);
	}
	
	public Object clone() {
		Object leClone = null;
		try {
			leClone = super.clone();
		} catch (CloneNotSupportedException e) {
			throw new InternalError();
		}
		return leClone;
	}
}
