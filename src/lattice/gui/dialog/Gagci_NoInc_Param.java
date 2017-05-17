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

package lattice.gui.dialog;

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.ListSelectionModel;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import lattice.gui.RelationalContextEditor;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.structure.CompleteConceptLattice;

/**
 * @author roume To change this generated comment edit the template variable
 *         "typecomment": Window>Preferences>Java>Templates. To enable and
 *         disable the creation of type comments go to
 *         Window>Preferences>Java>Code Generation.
 */
public class Gagci_NoInc_Param extends JDialog implements ActionListener,
        ListSelectionListener {

    private static int BACK = 0;

    private static int NEXT = 1;

    private static int TERMINATED = 2;

    private static int CANCELLED = -1;

    private static int Status = 0;

    private Vector lesBinRel = null;

    private static Vector setOfKi = new Vector();

    private static Vector setOfKiRelation = new Vector();

    private RelationalContextFamily relCtx = null;

    private JButton nextButton = new JButton("Next >");

    private JButton backButton = new JButton("< Back");

    private JButton cancelButton = new JButton("Cancel");

    private JButton terminatedButton = new JButton("Terminated");

    private JList allBinaryRelations = null;

    private JList listOfKi1 = null;

    private JList listOfKi2 = null;

    private JList allInterObjectBinaryRelations = null;

    private JPanel kiSeletionPanel = new JPanel(new BorderLayout());

    private JPanel kiRelationSeletionPanel = new JPanel(new BorderLayout());

    private Hashtable graphSelection = null;

    private static Hashtable lesGraphInit = new Hashtable();

    private JList lesKiFin = null;

    private Vector lesGraph = null;

    private JList shgGraph = null;

    private JPanel initGraphPanel = new JPanel(new BorderLayout());

    /**
     * Constructor for Gagci_NoInc_Param.
     * 
     * @throws HeadlessException
     */
    private Gagci_NoInc_Param(RelationalContextFamily relCtx) {
        super();
        this.relCtx = relCtx;
        nextButton.addActionListener(this);
        backButton.addActionListener(this);
        cancelButton.addActionListener(this);
        terminatedButton.addActionListener(this);

        lesBinRel = new Vector();
        for (int i = 0; i < relCtx.size(); i++) {
            if (relCtx.get(i) instanceof MatrixBinaryRelationBuilder)
                lesBinRel.add(relCtx.get(i));
        }
        allBinaryRelations = new JList(lesBinRel);
        allBinaryRelations
                .setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);
        allBinaryRelations.addListSelectionListener(this);

        initKiSelectionPanel();

        lesGraph = new Vector();
        for (int i = 0; i < relCtx.size(); i++) {
            if (relCtx.get(i) instanceof MatrixBinaryRelationBuilder
                && relCtx.get(i).getLattice() != null
                && relCtx.get(i).getLattice() instanceof CompleteConceptLattice)
                lesGraph.add(relCtx.get(i));
        }
        shgGraph = new JList((Vector) lesGraph);
        shgGraph.addListSelectionListener(this);
        shgGraph.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);

        setResizable(false);
        setSize(300, 150);
        // setSize(kiSeletionPanel.getSize());
        setContentPane(kiSeletionPanel);
        setTitle("Select Binary Relation...");
        setVisible(false);
        setModal(true);
    }

    /**
     * Returns the setOfKi.
     * 
     * @return Vector
     */
    public static Vector getSetOfKi() {
        return setOfKi;
    }

    /**
     * Returns the setOfKiRelation.
     * 
     * @return Vector
     */
    public static Vector getSetOfKiRelation() {
        return setOfKiRelation;
    }

    public static Hashtable getLesGraphInit() {
        return lesGraphInit;
    }

    private void initKiSelectionPanel() {

        kiSeletionPanel = new JPanel(new BorderLayout());

        JScrollPane scp = new JScrollPane(
                                          allBinaryRelations,
                                          JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
                                          JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);

        JPanel panel = new JPanel(new FlowLayout());
        panel.add(nextButton);
        panel.add(cancelButton);

        kiSeletionPanel.add(scp, BorderLayout.CENTER);
        kiSeletionPanel.add(panel, BorderLayout.SOUTH);

    }

    private void initRelationSelectionPanel() {

        listOfKi1 = new JList((Vector) setOfKi.clone());
        listOfKi1.addListSelectionListener(this);
        listOfKi1.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        listOfKi2 = new JList((Vector) setOfKi.clone());
        listOfKi2.addListSelectionListener(this);
        listOfKi2.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);

        setOfKiRelation.removeAllElements();
        for (int i = 0; i < setOfKi.size(); i++)
            setOfKiRelation.add(new Hashtable());

        JScrollPane scp1 = new JScrollPane(
                                           listOfKi1,
                                           JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
                                           JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
        JScrollPane scp2 = new JScrollPane(
                                           listOfKi2,
                                           JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
                                           JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
        JScrollPane scp3 = new JScrollPane(
                                           allInterObjectBinaryRelations,
                                           JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
                                           JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);

        JLabel lab1 = new JLabel("Select Ki:");
        JLabel lab2 = new JLabel("Select Kj:");
        JLabel lab3 = new JLabel("Select O(Ki) => O(Kj) Relational Attributes");

        GridBagLayout gridbag = new GridBagLayout();
        kiRelationSeletionPanel = new JPanel(gridbag);
        GridBagConstraints c = new GridBagConstraints();
        c.fill = GridBagConstraints.BOTH;
        c.gridwidth = 2;
        c.gridheight = 1;
        c.gridx = 0;
        c.gridy = 0;
        c.weighty = 1.0;
        kiRelationSeletionPanel.add(lab1, c);
        c.gridx = 2;
        c.gridy = 0;
        c.weighty = 1.0;
        kiRelationSeletionPanel.add(lab2, c);
        c.gridx = 0;
        c.gridy = 1;
        c.weighty = 4.0;
        kiRelationSeletionPanel.add(scp1, c);
        c.gridx = 2;
        c.gridy = 1;
        c.weighty = 4.0;
        kiRelationSeletionPanel.add(scp2, c);
        c.gridx = 0;
        c.gridy = 2;
        c.weighty = 1.0;
        c.gridwidth = 4;
        kiRelationSeletionPanel.add(lab3, c);
        c.gridx = 0;
        c.gridy = 3;
        c.weighty = 4.0;
        c.gridwidth = 4;
        kiRelationSeletionPanel.add(scp3, c);
        c.weighty = 1.0;
        c.gridy = 4;
        c.gridwidth = 1;
        kiRelationSeletionPanel.add(backButton, c);
        c.gridx++;
        kiRelationSeletionPanel.add(nextButton, c);
        c.weightx = 1.0;
        c.gridx++;
        c.gridwidth = 2;
        kiRelationSeletionPanel.add(cancelButton, c);

    }

    private void initGraphPanel() {
        graphSelection = new Hashtable();

        lesKiFin = new JList((Vector) setOfKi.clone());
        lesKiFin.addListSelectionListener(this);
        lesKiFin.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);

        JScrollPane scp1 = new JScrollPane(
                                           lesKiFin,
                                           JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
                                           JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
        JScrollPane scp2 = new JScrollPane(
                                           shgGraph,
                                           JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
                                           JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);

        JLabel lab1 = new JLabel("Select Ki:");
        JLabel lab2 = new JLabel("Select Graph Init. for Ki");

        GridBagLayout gridbag = new GridBagLayout();
        initGraphPanel = new JPanel(gridbag);
        GridBagConstraints c = new GridBagConstraints();
        c.fill = GridBagConstraints.BOTH;
        c.gridwidth = 2;
        c.gridheight = 1;
        c.gridx = 0;
        c.gridy = 0;
        c.weighty = 1.0;
        initGraphPanel.add(lab1, c);
        c.gridx = 2;
        c.gridy = 0;
        c.weighty = 1.0;
        initGraphPanel.add(lab2, c);
        c.gridx = 0;
        c.gridy = 1;
        c.weighty = 4.0;
        initGraphPanel.add(scp1, c);
        c.gridx = 2;
        c.gridy = 1;
        c.weighty = 4.0;
        initGraphPanel.add(scp2, c);
        c.weighty = 1.0;
        c.gridy = 2;
        c.gridx = 0;
        c.gridwidth = 1;
        initGraphPanel.add(backButton, c);
        c.gridx++;
        initGraphPanel.add(cancelButton, c);
        c.weightx = 1.0;
        c.gridx++;
        c.gridwidth = 2;
        initGraphPanel.add(terminatedButton, c);

    }

    /**
     * @see javax.swing.event.ListSelectionListener#valueChanged(javax.swing.event.ListSelectionEvent)
     */
    public void valueChanged(ListSelectionEvent arg0) {
        if (arg0.getSource() == allBinaryRelations) {
            setOfKi.removeAllElements();
            if (allBinaryRelations.getSelectedIndex() != -1) {
                for (int i = 0; i < allBinaryRelations.getSelectedValues().length; i++) {
                    setOfKi.add(allBinaryRelations.getSelectedValues()[i]);
                }
            }
        }
        if (arg0.getSource() == listOfKi1 || arg0.getSource() == listOfKi2) {
            if (listOfKi1.getSelectedIndex() != -1
                && listOfKi2.getSelectedIndex() != -1) {
                MatrixBinaryRelationBuilder theRel1 = (MatrixBinaryRelationBuilder) listOfKi1
                        .getSelectedValue();
                MatrixBinaryRelationBuilder theRel2 = (MatrixBinaryRelationBuilder) listOfKi2
                        .getSelectedValue();
                Vector theRels = (Vector) ((Hashtable) setOfKiRelation
                        .elementAt(listOfKi1.getSelectedIndex())).get(theRel2
                        .getName());
            }
        }
        if (arg0.getSource() == lesKiFin) {
            if (graphSelection.get(lesKiFin.getSelectedValue().toString()) != null) {
                shgGraph.clearSelection();
                shgGraph.setSelectedIndex(((Integer) graphSelection
                        .get(lesKiFin.getSelectedValue().toString()))
                        .intValue());
            }
        }
        if (arg0.getSource() == shgGraph) {
            if (lesKiFin.getSelectedIndex() == -1)
                shgGraph.clearSelection();
            else {
                graphSelection.put(lesKiFin.getSelectedValue().toString(),
                                   new Integer(shgGraph.getSelectedIndex()));
            }
        }

    }

    /**
     * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
     */
    public void actionPerformed(ActionEvent arg0) {

        if (arg0.getSource() == nextButton
            && getContentPane() == kiRelationSeletionPanel) {
            if (setOfKi.size() > 0) {
                Status = NEXT;
                setVisible(false);
                initGraphPanel();
                setSize(300, 250);
                // setSize(kiRelationSeletionPanel.getSize());
                remove(getContentPane());
                setContentPane(initGraphPanel);
                setTitle("Select Graph Init...");
                show();
            }
        }

        if ((arg0.getSource() == nextButton && getContentPane() == kiSeletionPanel)
            || (arg0.getSource() == backButton && getContentPane() == initGraphPanel)) {
            if (setOfKi.size() > 0) {
                Status = NEXT;
                setVisible(false);
                initRelationSelectionPanel();
                setSize(300, 400);
                // setSize(kiRelationSeletionPanel.getSize());
                remove(getContentPane());
                setContentPane(kiRelationSeletionPanel);
                setTitle("Select Relational Attributes...");
                show();
            }
        }
        if (arg0.getSource() == backButton
            && getContentPane() == kiRelationSeletionPanel) {
            Status = BACK;
            setVisible(false);
            initKiSelectionPanel();
            // setSize(kiSeletionPanel.getSize());
            setSize(300, 150);
            allInterObjectBinaryRelations.clearSelection();
            remove(getContentPane());
            setContentPane(kiSeletionPanel);
            setTitle("Select Binary Relation...");
            show();
        }
        if (arg0.getSource() == terminatedButton) {
            for (Enumeration iter = graphSelection.keys(); iter
                    .hasMoreElements();) {
                String Ki_name = (String) iter.nextElement();
                lesGraphInit.put(Ki_name, ((RelationBuilder) lesGraph
                        .elementAt(((Integer) graphSelection.get(Ki_name))
                                .intValue())).getLattice());
            }
            Status = TERMINATED;
            dispose();
        }
        if (arg0.getSource() == cancelButton) {
            Status = CANCELLED;
            dispose();
        }
    }

    public static boolean askParameter(RelationalContextFamily relCtx,
                                       RelationalContextEditor controler) {
        if (controler != null)
            controler.setEnabled(false);
        Gagci_NoInc_Param fen = new Gagci_NoInc_Param(relCtx);
        fen.setVisible(true);
        if (controler != null)
            controler.setEnabled(true);
        return Status == TERMINATED;
    }

}
