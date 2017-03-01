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

package rule.algorithm;

/**
 * <p>Titre : Petko&al 2</p>
 * <p>Description : PetkoInc (plate forme)</p>
 * ValtchevEtAl
 * <p>Copyright : Copyright (c) 2003</p>
 * <p>Soci�t� : UQAM - UdM</p>
 * @author non attribuable
 * @version 2.0
 */

// import java
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import lattice.util.structure.CompleteConceptLattice;
import rule.util.Rule;

public class ValtchevAlOnlineBasisUpdate extends AbstractRuleAlgorithm {

  public static final String EXACT_RULES = "0";
  public static final String APPROXIMATIVE_RULES = "1";
  public static final String BOTH = "2";

  private Set<Rule> approxRuleBasis = new HashSet<Rule>();
  private Set<Rule> exactRuleBasis = new HashSet<Rule>();

  private double confianceUsager;

  private String choix;

  // Variables de travail

  public ValtchevAlOnlineBasisUpdate(CompleteConceptLattice treillis, double minConfiance) {
    super(treillis, minConfiance, 0.0);
    confianceUsager = minConfiance;
  }

  public ValtchevAlOnlineBasisUpdate(CompleteConceptLattice treillis, double minConfiance, String choice) {
     super(treillis, minConfiance, 0.0);
     confianceUsager = minConfiance;
     choix = choice;
  }

// CONSTRUCTEUR

  /**
	 * Génération de l'ensemble des règles de la base générique.
	 * 
	 * @see rule.algorithm.AbstractRuleAlgorithm#doAlgorithm()
	 */
	public void doAlgorithm() {

		InformativeBasis infoBasis = new InformativeBasis(getLattice(),
				confianceUsager);
		GenericBasis genBasis = new GenericBasis(getLattice(), confianceUsager);
		super.doAlgorithm();

		if (choix.equals(EXACT_RULES)) {
			genBasis.doAlgorithm();
			exactRuleBasis = genBasis.getBase();
		} else if (choix.equals(APPROXIMATIVE_RULES)) {
			infoBasis.doAlgorithm();
			approxRuleBasis = infoBasis.getBase();
		} else if (choix.equals(BOTH)) {
			genBasis.doAlgorithm();
			infoBasis.doAlgorithm();
			exactRuleBasis = genBasis.getBase();
			approxRuleBasis = infoBasis.getBase();
		}
		affResults();
	}
	
	public Set<Rule> getExactRuleBasis() {
		return exactRuleBasis;
	}

	public Set<Rule> getApproxRuleBasis() {
		return approxRuleBasis;
	}

  /**
	 * Affichage des résultats dans la console
	 */
	public void affResults() {
		int i = 1;
		StringBuffer resultat = getStringResult();
		resultat.append("Approximative rule Base (Informative):" + "\n");
		Iterator<Rule> it = approxRuleBasis.iterator();
		while (it.hasNext())
			resultat.append("R" + i++ + " : " + it.next().toString() + "\n");
		resultat.append("Exact rule Base (Générique):" + "\n");
		i = 1;
		it = exactRuleBasis.iterator();
		while (it.hasNext())
			resultat.append("R" + i++ + " : " + it.next().toString() + "\n");
	}

/** 
 * Affichage
 */
  public String getDescription() {
    String desc = new String(
        "Valtchev & al. incremental basis update");
    return desc;
  }

  /* (non-Javadoc)
   * @see java.lang.Runnable#run()
   */

  public void run() {
    doAlgorithm();
    if (jobObserv != null)
      jobObserv.jobEnd(true);
  }

}