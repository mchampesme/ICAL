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

/*
 * Created on 12 juil. 2003 To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package lattice.gui.controller;

import java.awt.event.ActionEvent;
import java.util.Hashtable;
import java.util.Vector;

import javax.swing.JMenu;
import javax.swing.JMenuItem;

import lattice.algorithm.LatticeAlgorithm;
import lattice.algorithm.task.LatticeAlgorithmTask;
import lattice.gsh.algorithm.CERES;
import lattice.gui.RelationalContextEditor;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.ScalingBinaryRelation;
import lattice.util.structure.LatticeGraph;

/**
 * @author roume To change the template for this generated type comment go to
 *         Window>Preferences>Java>Code Generation>Code and Comments
 */
public class GSHController extends AbstractController {

    // Le menu et sous menu Algorithms
    private JMenu menuShg = null;

    private JMenuItem algoCeres = null;

    private JMenuItem algoAresCons = null;

    private JMenuItem algoGodinShg = null;

    private JMenu menuOp;

    private JMenuItem algoAres = null;

    private JMenuItem algoAresDual = null;

    private JMenu menuIcg;

    private JMenuItem umlApplication = null;

    private LatticeAlgorithmTask theTask = null;

    /**
	 * 
	 */
    public GSHController(RelationalContextEditor rce) {
        super(rce);
        initMenu();
        theTask = new LatticeAlgorithmTask(rce);
    }

    public void initMenu() {

        menuShg = new JMenu("Galois Sub-Hierarchy");
        menuShg.setMnemonic('G');

        algoCeres = new JMenuItem("CERES");
        algoCeres.setMnemonic('C');
        algoCeres.addActionListener(this);
        menuShg.add(algoCeres);

        algoAresCons = new JMenuItem("ARES Iterative Construction");
        algoAresCons.setMnemonic('A');
        algoAresCons.addActionListener(this);
        menuShg.add(algoAresCons);

        algoGodinShg = new JMenuItem("Godin SHG");
        algoGodinShg.setMnemonic('G');
        algoGodinShg.addActionListener(this);
        menuShg.add(algoGodinShg);

        menuOp = new JMenu("Maintaining SHG");
        menuOp.setMnemonic('M');

        algoAres = new JMenuItem("ARES: Add a Formal Object");
        algoAres.setMnemonic('O');
        algoAres.addActionListener(this);
        menuOp.add(algoAres);

        algoAresDual = new JMenuItem("ARES dual: Add a Formal Attribute");
        algoAresDual.setMnemonic('A');
        algoAresDual.addActionListener(this);
        menuOp.add(algoAresDual);

        menuShg.add(menuOp);

        menuIcg = new JMenu("Iterative Cross Generalization");
        menuIcg.setMnemonic('I');

        umlApplication = new JMenuItem("UML application: batch ");
        umlApplication.setMnemonic('U');
        umlApplication.addActionListener(this);
        menuIcg.add(umlApplication);

        menuShg.add(menuIcg);

    }

    public JMenu getMainMenu() {
        return menuShg;
    }

    /*
     * (non-Javadoc)
     * @see
     * java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
     */
    public void actionPerformed(ActionEvent arg0) {
        if (arg0.getSource() == algoCeres) {
            execAlgorithm(new CERES(
                                    (MatrixBinaryRelationBuilder) rce
                                            .getSelectedRelation()));
        }
        if (arg0.getSource() == algoAresCons) {
            rce.addMessage("This Algorithm AresConstruction is not yet imlemented!\n");
        }
        if (arg0.getSource() == algoGodinShg) {
            rce.addMessage("This Algorithm is not yet imlemented!\n");
        }
        if (arg0.getSource() == algoAres) {
            rce.addMessage("This Algorithm Ares is not yet imlemented!\n");
        }
        if (arg0.getSource() == algoAresDual) {
            rce.addMessage("This Algorithm AresDual is not yet imlemented!\n");
        }
        rce.checkPossibleActions();
    }

    protected void execAlgorithm(LatticeAlgorithm algo) {
        rce.setWorkOnRelation(algo.getBinaryRelation()); // marquer la relation
                                                         // 'On Use'
        Vector binRelOnUse = new Vector();

        binRelOnUse.add(algo.getBinaryRelation());

        theTask.setBinRelOnUse(binRelOnUse);
        theTask.setAlgo(algo);
        theTask.exec();
    }

    public void checkPossibleActions() {

        if (rce.getFamilyContexts().size() == 0) {
            menuShg.setEnabled(false);
            return;
        }

        RelationBuilder absRel = rce.getSelectedRelation();

        if (absRel instanceof MatrixBinaryRelationBuilder) {
            if (rce.isOnWork(absRel))
                menuShg.setEnabled(false);
            else {
                menuShg.setEnabled(true);
                if (absRel.getLattice() != null
                    && absRel.getLattice() instanceof LatticeGraph) {
                    algoAres.setEnabled(true);
                    algoAresDual.setEnabled(true);
                } else {
                    algoAres.setEnabled(false);
                    algoAresDual.setEnabled(false);
                }
            }
        }

        if (absRel instanceof ScalingBinaryRelation) {
            menuShg.setEnabled(false);
        }
    }

}
