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
 * <p>Soci�t� : UQAM - UdM</p>
 * @author frambourg_c
 * @version 1.0
 */

import java.awt.event.ActionEvent;
import java.util.Iterator;
import java.util.Vector;

import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;

import lattice.algorithm.LatticeAlgorithmInc;
import lattice.algorithm.ValtchevEtAl2;
import lattice.algorithm.merge.AttributeMerge;
import lattice.algorithm.merge.ContextSplit;
import lattice.algorithm.merge.DivideAndConquer;
import lattice.algorithm.merge.ObjectMerge;
import lattice.algorithm.task.LatticeAlgorithmTask;
import lattice.gui.RelationalContextEditor;
import lattice.gui.dialog.ChoiceDialogSelection;
import lattice.gui.graph.LatticeGraphFrame;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.relation.ScalingBinaryRelation;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
import rule.generator.Jen;

/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */

public class MergeController
    extends AbstractController {

  private JMenu menuTrellit = null;
  private JMenu menuTreilliO = null;
  private JMenu menuTreilliA = null;
  private JMenuItem dAcO = null;
  private JMenuItem dCO = null;
  private JMenuItem extractO = null;
  private JMenuItem dAcA = null;
  private JMenuItem dCA = null;
  private JMenuItem extractA = null;

  private LatticeAlgorithmTask theTask = null;

  /**
   * @param rce
   */
  public MergeController(RelationalContextEditor rce) {
    super(rce);
    initMenu();
    theTask = new LatticeAlgorithmTask(rce);
  }

  public void initMenu() {

    menuTrellit = new JMenu("Merge lattices");
    menuTrellit.setMnemonic('U');

    menuTreilliO = new JMenu("by Objects");
    menuTreilliO.setMnemonic('O');
    menuTrellit.add(menuTreilliO);

    menuTreilliA = new JMenu("by Attributes");
    menuTreilliA.setMnemonic('A');
    menuTrellit.add(menuTreilliA);

    // Les Items
    dCO = new JMenuItem("by two different contexts");
    dCO.addActionListener(this);
    menuTreilliO.add(dCO);
    dCA = new JMenuItem("by two different contexts");
    dCA.addActionListener(this);
    menuTreilliA.add(dCA);

    extractO = new JMenuItem("by the extraction from a context");
    extractO.addActionListener(this);
    menuTreilliO.add(extractO);
    extractA = new JMenuItem("by the extraction from a context");
    extractA.addActionListener(this);
    menuTreilliA.add(extractA);

    dAcO = new JMenuItem("Divide & Conquer");
    dAcO.addActionListener(this);
    menuTreilliO.add(dAcO);
    dAcA = new JMenuItem("Divide & Conquer");
    dAcA.addActionListener(this);
    menuTreilliA.add(dAcA);

  }

  public JMenu getMainMenu() {
    return menuTrellit;
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0) {
    boolean gens = true;
    JFrame frame = new JFrame();
    if (arg0.getSource() == dCO || arg0.getSource() == extractO ||
        arg0.getSource() == dAcO) {
      int choix = JOptionPane.showConfirmDialog(frame,
                                                "Do you want the generators to be calculated?",
                                                "Generators Choice",
                                                JOptionPane.YES_NO_OPTION);
      if (choix == JOptionPane.YES_OPTION)
        gens = true;
      else
        gens = false;
      if (arg0.getSource() == dCO) {
        RelationalContextFamily rc = rce.getFamilyContexts();
        ChoiceDialogSelection eds = new ChoiceDialogSelection(rc, rce,
            "Select the contexts of the two lattices you want to merge:");
        eds.askParameter();
        if (eds.getAction() == ChoiceDialogSelection.CANCELLED) {
          addMessage("Selection Cancelled!\n");
          return;
        }
        if (eds.getData() == null) {
          addMessage("No data selected!");
          addMessage("Selection Cancelled!\n");
          return;
        }
        else {
          JList theList = new JList();
          MatrixBinaryRelationBuilder[] rels = new MatrixBinaryRelationBuilder[2];
          rc = (RelationalContextFamily) eds.getData();
          if (rc.size() == 2) {
            for (int i = 0; i < rc.size(); i++) {
              rels[i] = ( (MatrixBinaryRelationBuilder) rc.get(i));
            }
            MatrixBinaryRelationBuilder br1 = rels[0];
            MatrixBinaryRelationBuilder br2 = rels[1];
            CompleteConceptLattice lat1;
            CompleteConceptLattice lat2;
            if (br1.getLattice() == null) {
              LatticeAlgorithmInc algo = new ValtchevEtAl2(br1, gens);
              algo.doAlgorithm();
              lat1 = algo.getLattice();
              br1.setLattice(lat1);
            }
            else {
              lat1 = br1.getLattice();
              if (gens) {
                Iterator it = lat1.iterator();
                it.next();
                if ( ( (ConceptNode) (it.next())).getContent().getGenerator().size() ==
                    0) {
                  Jen jen = new Jen(br1.getLattice());
                  jen.calculGenerateurs();
                }
              }
            }
            LatticeGraphFrame f = new LatticeGraphFrame("Lattice 1 : " +
                br1.getName(), lat1.getTop());
            f.show();
            if (br2.getLattice() == null) {
              LatticeAlgorithmInc algo = new ValtchevEtAl2(br2, gens);
              algo.doAlgorithm();
              lat2 = algo.getLattice();
              br2.setLattice(lat2);
            }
            else {
              lat2 = br2.getLattice();
              if (gens) {
                Iterator it = lat2.iterator();
                it.next();
                if ( ( (ConceptNode) (it.next())).getContent().getGenerator().size() ==
                    0) {
                  Jen jen = new Jen(br2.getLattice());
                  jen.calculGenerateurs();
                }

              }

            }
            f = new LatticeGraphFrame("Lattice 2 : " + br2.getName(),
                                      lat2.getTop());
            f.show();
            ConceptNodeImp.resetNodeId();
            CompleteConceptLattice lat3 = ObjectMerge.
                fusionne(lat1, lat2,
                         br1, br2, gens);
            MatrixBinaryRelationBuilder br = ObjectMerge.createBR(br1, br2);
            rce.addBinaryRelation(br);
            br.setLattice(lat3);
            if (lat3 != null) {
              f = new LatticeGraphFrame("Fusion of the two lattices",
                                        lat3.getTop());
              f.show();
            }
          }
          else if (rc.size() > 2) {
            JOptionPane.showMessageDialog(frame,
                                          "You have selected more than two contexts");
            addMessage("Too much data selected!");
            addMessage("Selection Cancelled!\n");
          }
          else {
            JOptionPane.showMessageDialog(frame,
                                          "You have selected less than two contexts");
            addMessage("not enough data selected!");
            addMessage("Selection Cancelled!\n");
          }
        }
      }
      if (arg0.getSource() == extractO) {
        ChoiceDialogSelection eds = new ChoiceDialogSelection(rce.
            getSelectedRelation(), "objects",
            "Select the objects on which you want to base the merge",
            "Don't select anything if you just want the context to be cut by half:");
        eds.askParameter();
        if (eds.getAction() == ChoiceDialogSelection.CANCELLED) {
          addMessage("Selection Cancelled!\n");
          return;
        }
        if (eds.getData() == null &&
            eds.getAction() == ChoiceDialogSelection.SELECT) {
          MatrixBinaryRelationBuilder br = (MatrixBinaryRelationBuilder) rce.getSelectedRelation();
          Object[][] ls = ContextSplit.cutO(rce, br, gens);
          CompleteConceptLattice lat1 = (CompleteConceptLattice) ls[0][0];
          CompleteConceptLattice lat2 = (CompleteConceptLattice) ls[1][0];
          MatrixBinaryRelationBuilder br1 = (MatrixBinaryRelationBuilder) ls[0][1];
          MatrixBinaryRelationBuilder br2 = (MatrixBinaryRelationBuilder) ls[1][1];
          br1.setLattice(lat1);
          br2.setLattice(lat2);
          LatticeGraphFrame f = new LatticeGraphFrame("Lattice 1 : " +
              lat1.getDescription(),
              lat1.getTop());
          f.show();
          f = new LatticeGraphFrame("Lattice 2 : " + lat2.getDescription(),
                                    lat2.getTop());
          f.show();
          ConceptNodeImp.resetNodeId();
          CompleteConceptLattice lat3 = ObjectMerge.fusionne(lat1, lat2,
              br1, br2, gens);
          br.setLattice(lat3);
          if (lat3 != null) {
            f = new LatticeGraphFrame("Fusion of the two lattices", lat3.getTop());
            f.show();
          }
        }
        else if (eds.getData() == null) {
          addMessage("No data selected!");
          addMessage("Selection Cancelled!\n");
          return;
        }
        else {
          Vector o = new Vector();
          o = (Vector) eds.getData();
          MatrixBinaryRelationBuilder br = (MatrixBinaryRelationBuilder) rce.getSelectedRelation();
          Object[][] ls = ContextSplit.cutO(rce, br, o, gens);
          CompleteConceptLattice lat1 = (CompleteConceptLattice) ls[0][0];
          CompleteConceptLattice lat2 = (CompleteConceptLattice) ls[1][0];
          MatrixBinaryRelationBuilder br1 = (MatrixBinaryRelationBuilder) ls[0][1];
          MatrixBinaryRelationBuilder br2 = (MatrixBinaryRelationBuilder) ls[1][1];
          br1.setLattice(lat1);
          br2.setLattice(lat2);
          LatticeGraphFrame f = new LatticeGraphFrame("Lattice 1 : " +
              lat1.getDescription(),
              lat1.getTop());
          f.show();
          f = new LatticeGraphFrame("Lattice 2 : " + lat2.getDescription(),
                                    lat2.getTop());
          f.show();
          ConceptNodeImp.resetNodeId();
          CompleteConceptLattice lat3 = ObjectMerge.fusionne(lat1, lat2,
              br1, br2, gens);
          br.setLattice(lat3);
          if (lat3 != null) {
            f = new LatticeGraphFrame("Fusion of the two lattices", lat3.getTop());
            f.show();
          }
        }

      }
      if (arg0.getSource() == dAcO) {
        MatrixBinaryRelationBuilder br = (MatrixBinaryRelationBuilder) rce.getSelectedRelation();
        CompleteConceptLattice lat3 = DivideAndConquer.constructO(br, 0,
            br.getObjectsNumber() - 1, gens);
        if (lat3 != null) {
          br.setLattice(lat3);
          LatticeGraphFrame f = new LatticeGraphFrame(
              "Lattice constructed by the divide and conquer method",
              lat3.getTop());
          f.show();
        }
      }
    }
    if (arg0.getSource() == dCA) {
      RelationalContextFamily rc = rce.getFamilyContexts();
      ChoiceDialogSelection eds = new ChoiceDialogSelection(rc, rce,
          "Select the contexts of the two lattices you want to merge:");
      eds.askParameter();
      if (eds.getAction() == ChoiceDialogSelection.CANCELLED) {
        addMessage("Selection Cancelled!\n");
        return;
      }
      if (eds.getData() == null) {
        addMessage("No data selected!");
        addMessage("Selection Cancelled!\n");
        return;
      }
      else {
        JList theList = new JList();
        MatrixBinaryRelationBuilder[] rels = new MatrixBinaryRelationBuilder[2];
        rc = (RelationalContextFamily) eds.getData();
        if (rc.size() == 2) {
          for (int i = 0; i < rc.size(); i++) {
            rels[i] = ( (MatrixBinaryRelationBuilder) rc.get(i));
          }
          MatrixBinaryRelationBuilder br1 = rels[0];
          MatrixBinaryRelationBuilder br2 = rels[1];
          CompleteConceptLattice lat1;
          CompleteConceptLattice lat2;
          if (br1.getLattice() == null) {
            LatticeAlgorithmInc algo = new ValtchevEtAl2(br1);
            algo.doAlgorithm();
            lat1 = algo.getLattice();
            br1.setLattice(lat1);
          }
          else {
            lat1 = br1.getLattice();
            /*if (gens) {
              Iterator it = lat1.iterator();
              it.next();
              if ( ( (Node) (it.next())).getConcept().getGenerator().size() ==
                  0) {
                Jen jen = new Jen(br1.getLattice());
                jen.calculGenerateurs();
              }
                         }*/
          }
          LatticeGraphFrame f = new LatticeGraphFrame("Lattice 1 : " +
              br1.getName(), lat1.getTop());
          f.show();
          if (br2.getLattice() == null) {
            LatticeAlgorithmInc algo = new ValtchevEtAl2(br2, gens);
            algo.doAlgorithm();
            lat2 = algo.getLattice();
            br2.setLattice(lat2);
          }
          else {
            lat2 = br2.getLattice();
            /*if (gens) {
              Iterator it = lat2.iterator();
              it.next();
              if ( ( (Node) (it.next())).getConcept().getGenerator().size() ==
                  0) {
                Jen jen = new Jen(br2.getLattice());
                jen.calculGenerateurs();
              }

                         }*/

          }
          f = new LatticeGraphFrame("Lattice 2 : " + br2.getName(),
                                    lat2.getTop());
          f.show();
          ConceptNodeImp.resetNodeId();
          CompleteConceptLattice lat3 = AttributeMerge.
              fusionne(lat1, lat2,
                       br1, br2);
          MatrixBinaryRelationBuilder br = AttributeMerge.createBR(br1, br2);
          rce.addBinaryRelation(br);
          br.setLattice(lat3);
           if (lat3 != null) {
            f = new LatticeGraphFrame("Fusion of the two lattices",
                                      lat3.getTop());
            f.show();
          }
        }
        else if (rc.size() > 2) {
          JOptionPane.showMessageDialog(frame,
                                        "You have selected more than two contexts");
          addMessage("Too much data selected!");
          addMessage("Selection Cancelled!\n");
        }
        else {
          JOptionPane.showMessageDialog(frame,
                                        "You have selected less than two contexts");
          addMessage("not enough data selected!");
          addMessage("Selection Cancelled!\n");
        }
      }
    }
    if (arg0.getSource() == extractA) {
      ChoiceDialogSelection eds = new ChoiceDialogSelection(rce.
          getSelectedRelation(), "attributes",
          "Select the attributes on which you want to base the merge:",
          "Don't select anything if you just want the context to be cut by half:");
      eds.askParameter();
      if (eds.getAction() == ChoiceDialogSelection.CANCELLED) {
        addMessage("Selection Cancelled!\n");
        return;
      }
      if (eds.getData() == null &&
          eds.getAction() == ChoiceDialogSelection.SELECT) {
        MatrixBinaryRelationBuilder br = (MatrixBinaryRelationBuilder) rce.getSelectedRelation();
        Object[][] ls = ContextSplit.cutA(rce, br);
        CompleteConceptLattice lat1 = (CompleteConceptLattice) ls[0][0];
        CompleteConceptLattice lat2 = (CompleteConceptLattice) ls[1][0];
        MatrixBinaryRelationBuilder br1 = (MatrixBinaryRelationBuilder) ls[0][1];
        MatrixBinaryRelationBuilder br2 = (MatrixBinaryRelationBuilder) ls[1][1];
        br1.setLattice(lat1);
        br2.setLattice(lat2);
        LatticeGraphFrame f = new LatticeGraphFrame("Lattice 1 : " +
            lat1.getDescription(),
            lat1.getTop());
        f.show();
        f = new LatticeGraphFrame("Lattice 2 : " + lat2.getDescription(),
                                  lat2.getTop());
        f.show();
        ConceptNodeImp.resetNodeId();
        CompleteConceptLattice lat3 = AttributeMerge.fusionne(lat1, lat2,
            br1, br2);
        br.setLattice(lat3);
        if (lat3 != null) {
          f = new LatticeGraphFrame("Fusion of the two lattices", lat3.getTop());
          f.show();
        }
      }
      else if (eds.getData() == null) {
        addMessage("No data selected!");
        addMessage("Selection Cancelled!\n");
        return;
      }
      else {
        Vector a = new Vector();
        a = (Vector) eds.getData();
        MatrixBinaryRelationBuilder br = (MatrixBinaryRelationBuilder) rce.getSelectedRelation();
        Object[][] ls = ContextSplit.cutA(rce, br, a);
        CompleteConceptLattice lat1 = (CompleteConceptLattice) ls[0][0];
        CompleteConceptLattice lat2 = (CompleteConceptLattice) ls[1][0];
        MatrixBinaryRelationBuilder br1 = (MatrixBinaryRelationBuilder) ls[0][1];
        MatrixBinaryRelationBuilder br2 = (MatrixBinaryRelationBuilder) ls[1][1];
        br1.setLattice(lat1);
        br2.setLattice(lat2);
        LatticeGraphFrame f = new LatticeGraphFrame("Lattice 1: " +
            lat1.getDescription(),
            lat1.getTop());
        f.show();
        f = new LatticeGraphFrame("Lattice 2: " + lat2.getDescription(),
                                  lat2.getTop());
        f.show();
        ConceptNodeImp.resetNodeId();
        CompleteConceptLattice lat3 = AttributeMerge.fusionne(lat1, lat2,
            br1, br2);
        br.setLattice(lat3);
        if (lat3 != null) {
          f = new LatticeGraphFrame("Fusion of the two lattices", lat3.getTop());
          f.show();
        }
      }
    }
    if (arg0.getSource() == dAcA) {
      MatrixBinaryRelationBuilder br = (MatrixBinaryRelationBuilder) rce.getSelectedRelation();
      CompleteConceptLattice lat3 = DivideAndConquer.constructA(br, 0,
          br.getAttributesNumber() - 1);
      if (lat3 != null) {
        br.setLattice(lat3);
        LatticeGraphFrame f = new LatticeGraphFrame(
            "Lattice constructed by the divide and conquer method",
            lat3.getTop());
        f.show();
      }
    }
    rce.checkPossibleActions();
  }

  protected void execAlgorithm(LatticeAlgorithmInc algo) {
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

  }
}
