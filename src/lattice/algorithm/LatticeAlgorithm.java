/*
 * **********************************************************************
 * Copyright (C) 2004 The Galicia Team Modifications to the initial code base
 * are copyright of their respective authors, or their employers as appropriate.
 * Authorship of the modifications may be determined from the ChangeLog placed
 * at the end of this file. This program is free software; you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of the
 * License, or (at your option) any later version. This program is distributed
 * in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even
 * the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details. You should have
 * received a copy of the GNU Lesser General Public License along with this
 * program; if not, write to the Free Software Foundation, Inc., 59 Temple
 * Place, Suite 330, Boston, MA 02111-1307 USA; or visit the following url:
 * http://www.gnu.org/copyleft/lesser.html
 * **********************************************************************
 */

package lattice.algorithm;

import lattice.gui.tooltask.AbstractJob;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.CompleteConceptLatticeImp;

/**
 * <p>
 * Title: Classe abstraite, racine des algo
 * </p>
 * <p>
 * Description:
 * </p>
 * <p>
 * Copyright: Copyright (c) 2002
 * </p>
 * <p>
 * Company:
 * </p>
 * 
 * @author David Grosser
 * @version 1.0
 */

public abstract class LatticeAlgorithm extends AbstractJob {

    private double minSupp;

    private CompleteConceptLattice lattice;

    private MatrixBinaryRelationBuilder binRel;

    public LatticeAlgorithm() {
        lattice = new CompleteConceptLatticeImp();
    }

    public LatticeAlgorithm(MatrixBinaryRelationBuilder bRel) {
        binRel = bRel;
        lattice = new CompleteConceptLatticeImp();
    }

    public void setminSupp(double e) {
        this.minSupp = e;
    }

    public double getminSupp() {
        return this.minSupp;
    }

    /**
     * @return lcl
     */
    public CompleteConceptLattice getLattice() {
        return lattice;
    }

    public MatrixBinaryRelationBuilder getBinaryRelation() {
        return binRel;
    }

    /**
     * @param lcl
     */
    public void setLattice(CompleteConceptLattice lcl) {
        this.lattice = lcl;
    }

    public abstract void doAlgorithm();

    public abstract String getDescription();

    // Implementation de ObservableWork
    public void run() {
        if (jobObserv != null) {
            jobObserv.sendMessage("Start : " + getDescription()
                                  + " on relation named "
                                  + binRel.getName());
        }

        doAlgorithm();
        lattice.setDescription(getDescription() + " - "
                               + binRel.getName() + " - #OfNodes = "
                               + lattice.size());
        binRel.setLattice(lattice);

        if (jobObserv != null) {
            jobObserv.sendMessage("End : " + getDescription()
                                  + " on relation named "
                                  + binRel.getName() + "\n");
            jobObserv.jobEnd(true);
        }
    }

}