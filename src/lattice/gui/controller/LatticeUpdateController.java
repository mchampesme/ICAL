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

package lattice.gui.controller;

/**
 * <p>Titre : Petko&al 2</p>
 * <p>Description : PetkoInc (plate forme)</p>
 * <p>Copyright : Copyright (c) 2003</p>
 * <p>Société : UQAM - UdM</p>
 * @author frambourg_c
 * @version 1.0
 */

import java.awt.event.ActionEvent;
import java.util.Vector;

import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;

import lattice.algorithm.LatticeAlgorithm;
import lattice.algorithm.LatticeAlgorithmInc;
import lattice.algorithm.ValtchevEtAl2;
import lattice.algorithm.task.LatticeAlgorithmTask;
import lattice.gui.RelationalContextEditor;
import lattice.gui.graph.LatticeGraphFrame;
import lattice.iceberg.algorithm.MagaliceA;
import lattice.iceberg.algorithm.MagaliceAGen;
import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.relation.ScalingBinaryRelation;
import lattice.util.structure.CompleteConceptLattice;
/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */

public class LatticeUpdateController
    extends AbstractController {

  private JMenu menuTrellit = null;
  private JMenuItem valNalAlgoAdd = null;
  private JMenuItem AttIncreAlgoAdd = null;
  private JMenuItem AttIncreAlgoRemove = null;

  private LatticeAlgorithmTask theTask = null;

  /**
   * @param rce
   */
  public LatticeUpdateController(RelationalContextEditor rce) {
    super(rce);
    initMenu();
    theTask = new LatticeAlgorithmTask(rce);
  }

  public void initMenu() {

    menuTrellit = new JMenu("Update the lattice");
    menuTrellit.setMnemonic('U');

    // Les Items
    valNalAlgoAdd = new JMenuItem("Add Object (Valtchev & al. v2)");
    valNalAlgoAdd.addActionListener(this);
    menuTrellit.add(valNalAlgoAdd);

	AttIncreAlgoAdd = new JMenuItem("Add Attribute (Magalice-A)");
	AttIncreAlgoAdd.addActionListener(this);
	menuTrellit.add(AttIncreAlgoAdd);
	   
	AttIncreAlgoRemove = new JMenuItem("Remove Attribute (Magalice-A)");
	AttIncreAlgoRemove.addActionListener(this);
	menuTrellit.add(AttIncreAlgoRemove);

  }

  public JMenu getMainMenu() {
    return menuTrellit;
  }

  /*
     * (non-Javadoc)
     * 
     * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
     */
    public void actionPerformed(ActionEvent arg0) {
        if (arg0.getSource() == valNalAlgoAdd) {
            MatrixBinaryRelationBuilder r = (MatrixBinaryRelationBuilder) rce
                    .getSelectedRelation();
            CompleteConceptLattice lat = r.getLattice();

            if (lat == null) {
                JFrame frame = new JFrame();
                int choix = JOptionPane
                        .showConfirmDialog(
                                           frame,
                                           "This context has no associated lattice graph.\nDo you want it to be calculated ?",
                                           "", JOptionPane.YES_NO_OPTION);
                if (choix == JOptionPane.YES_OPTION) {
                    LatticeAlgorithmInc algo = new ValtchevEtAl2(r, true);
                    algo.doAlgorithm();
                    r.setLattice(algo.getLattice());
                    LatticeGraphFrame f = new LatticeGraphFrame(algo
                            .getDescription(), algo.getLattice().getTop());
                    f.setVisible(true);
                } else
                    return;
            } else {
                LatticeAlgorithmInc algo = new ValtchevEtAl2(lat);
                Extent e = new SetExtent();
                Intent i = new SetIntent();
                if (lat.getTop().getContent().getExtent().size() != r
                        .getObjectsNumber()) {
                    e.add(r.getFormalObject(r.getObjectsNumber() - 1));
                    i = r
                            .getIntent(r
                                    .getFormalObject(r.getObjectsNumber() - 1));
                    ConceptImp c = new ConceptImp(e, i);
                    algo.addConcept(c);
                    r.setLattice(algo.getLattice());
                    LatticeGraphFrame f = new LatticeGraphFrame(algo
                            .getDescription(), algo.getLattice().getTop());
                    f.show();
                } else {
                    JFrame frame = new JFrame();
                    JOptionPane
                            .showMessageDialog(frame,
                                               "The context has not been modified");
                }
            }
        }

        if (arg0.getSource() == AttIncreAlgoAdd) {
            MatrixBinaryRelationBuilder r = (MatrixBinaryRelationBuilder) rce
                    .getSelectedRelation();
            CompleteConceptLattice lat = r.getLattice();
            if (lat == null) {
                JFrame frame = new JFrame();
                int choix = JOptionPane
                        .showConfirmDialog(
                                           frame,
                                           "This context has no associated lattice graph.\nDo you want it to be calculated ?",
                                           "", JOptionPane.YES_NO_OPTION);
                if (choix == JOptionPane.YES_OPTION) {
                    LatticeAlgorithmInc algo = new MagaliceAGen(r, lat
                            .getMinSupp());
                    algo.doAlgorithm();
                    r.setLattice(algo.getLattice());
                    LatticeGraphFrame f = new LatticeGraphFrame(algo
                            .getDescription(), algo.getLattice().getTop());
                    f.show();
                } else
                    return;
            } else {
                LatticeAlgorithmInc algo = new MagaliceAGen(lat, lat
                        .getMinSupp());
                // System.out.println("Iceberg for minSupp =
                // "+lat.getMinSupp());
                Extent e = new SetExtent();
                Intent i = new SetIntent();
                // System.out.println("Attributes No: "+r.getAttributeNumber());
                // System.out.println("Bottom Intent Size:
                // "+lat.getBottom().getConcept().getIntent().size());

                // Node nTest = (Node)lat.getTop().getChildren().get(0);
                // if (!nTest.getConcept().getGenerator().isEmpty())
                if (lat.getTop().getContent().getGenerator() != null)
                    algo = new MagaliceAGen(lat, lat.getMinSupp());

                else
                    algo = new MagaliceA(lat, lat.getMinSupp());

                if (lat.getBottom().getContent().getIntent().size() != r
                        .getAttributesNumber()) {
                    e = r.getExtent(r.getFormalAttribute(r
                            .getAttributesNumber() - 1));
                    i.add(r.getFormalAttribute(r.getAttributesNumber() - 1));
                    // e.add(r.getFormalObject(r.getObjectsNumber() - 1));
                    // i = r.getF(r.getFormalObject(r.getObjectsNumber() - 1));
                    // System.out.println("NEW EXTENT: "+e);
                    // System.out.println("NEW INTENT: "+i);

                    ConceptImp c = new ConceptImp(e, i);
                    algo.addConcept(c);
                    r.setLattice(algo.getLattice());
                    LatticeGraphFrame f = new LatticeGraphFrame(algo
                            .getDescription(), algo.getLattice().getTop());
                    f.show();
                } else {
                    JFrame frame = new JFrame();
                    JOptionPane
                            .showMessageDialog(frame,
                                               "The context has not been modified");
                }
            }
        }

        if (arg0.getSource() == AttIncreAlgoRemove) {
            MatrixBinaryRelationBuilder r = (MatrixBinaryRelationBuilder) rce
                    .getSelectedRelation();
            MatrixBinaryRelationBuilder br = (MatrixBinaryRelationBuilder) r
                    .clone();
            Concept conceptDeleted = (Concept) rce.removeAttribute();
            // r.setRelationName(r.getRelationName() +" "+ new
            // Integer(r.getAttributeNumber()).toString()+" Att");
            // addNewContext(r);
            br.setName(r.getName() + " ORIGINAL");
            rce.addBinaryRelation(br);
            // addNewContext(br);

            CompleteConceptLattice lat = r.getLattice();

            if (lat == null) {
                JFrame frame = new JFrame();
                int choix = JOptionPane
                        .showConfirmDialog(
                                           frame,
                                           "This context has no associated lattice graph.\nDo you want it to be calculated ?",
                                           "", JOptionPane.YES_NO_OPTION);
                if (choix == JOptionPane.YES_OPTION) {
                    LatticeAlgorithmInc algo = new MagaliceAGen(r, lat
                            .getMinSupp());
                    algo.doAlgorithm();
                    r.setLattice(algo.getLattice());
                    LatticeGraphFrame f = new LatticeGraphFrame(algo
                            .getDescription(), algo.getLattice().getTop());
                    f.show();
                } else
                    return;
            } else {
                LatticeAlgorithmInc algo = new MagaliceAGen(lat, lat
                        .getMinSupp());

                //Node nTest = (Node)lat.getTop().getChildren().get(0);
                //if (!nTest.getConcept().getGenerator().isEmpty())
                if (lat.getTop().getContent().getGenerator() != null)
                    algo = new MagaliceAGen(lat, lat.getMinSupp());
                else
                    algo = new MagaliceA(lat, lat.getMinSupp());

                System.out.println("Attribute removed (a',a) = ("
                                   + conceptDeleted.getExtent() + ","
                                   + conceptDeleted.getIntent() + ")");
                algo.deleteConcept(conceptDeleted);
                r.setLattice(algo.getLattice());
                LatticeGraphFrame f = new LatticeGraphFrame(algo
                        .getDescription(), algo.getLattice().getTop());
                f.show();
            }
        }

        rce.checkPossibleActions();
    }

  protected void execAlgorithm(LatticeAlgorithm algo) {
    rce.setWorkOnRelation(algo.getBinaryRelation()); // marquer la relation 'On Use'
    Vector binRelOnUse = new Vector();
    binRelOnUse.add(algo.getBinaryRelation());
    theTask.setBinRelOnUse(binRelOnUse);
    theTask.setAlgo(algo);
    theTask.exec();
  }

  public void checkPossibleActions() {

    if (rce.getFamilyContexts().size() == 0) {
      menuTrellit.setEnabled(false);
      return;
    }
    RelationBuilder absRel = rce.getSelectedRelation();
    if (absRel instanceof MatrixBinaryRelationBuilder) {
      menuTrellit.setEnabled(true);
      if (rce.isOnWork(absRel))
        menuTrellit.setEnabled(false);
      return;
    }
    if (absRel instanceof ScalingBinaryRelation) {
      menuTrellit.setEnabled(false);
      return;
    }
    if (absRel instanceof InterObjectBinaryRelation) {
      menuTrellit.setEnabled(false);
      return;
    }
  }
}