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

package lattice.gui;

import java.awt.HeadlessException;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.InputEvent;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.WindowEvent;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Vector;

import javax.swing.JFileChooser;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import lattice.algorithm.LatticeAlgorithm;
import lattice.algorithm.task.LatticeAlgorithmTask;
import lattice.alpha.gui.controller.AlphaController;
import lattice.alpha.util.Relation;
import lattice.database.gui.DatabaseController;
import lattice.database.task.DatabaseReadingTask;
import lattice.database.task.DatabaseWritingTask;
import lattice.database.util.DatabaseFunctions;
import lattice.gsh.algorithm.Gagci_NoInc;
import lattice.gui.controller.GSHController;
import lattice.gui.controller.IcebergController;
import lattice.gui.controller.LatticeController;
import lattice.gui.controller.LatticeUpdateController;
import lattice.gui.controller.MergeController;
import lattice.gui.controller.RCAController;
import lattice.gui.controller.RuleController;
import lattice.gui.dialog.ExportDialogSelection;
import lattice.gui.filter.XML_Filter;
import lattice.gui.graph.LatticeGraphFrame;
import lattice.gui.relation.AbstractRelationTableEditor;
import lattice.gui.relation.AbstractRelationTableModel;
import lattice.gui.relation.BinaryRelationTableEditor;
import lattice.gui.tooltask.AbstractTask;
import lattice.io.ConsoleWriter;
import lattice.io.XmlWriter;
import lattice.io.task.ReadingTask;
import lattice.io.task.WritingTask;
import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.relation.ScalingBinaryRelation;
import lattice.util.structure.CompleteConceptLattice;
import rule.gui.TableVisualization;
import rule.io.XmlRuleExport;
import rule.task.ruleAbstractTask;
import rule.util.Rule;
import rule.util.RulesBasis;

/**
 * @author Mr ROUME To change this generated comment edit the template variable
 *         "typecomment": Window>Preferences>Java>Templates. To enable and
 *         disable the creation of type comments go to
 *         Window>Preferences>Java>Code Generation.
 */
public class RelationalContextEditor extends OpenFileFrame implements
        ActionListener, MouseListener, ChangeListener {

    // Le Context Relationel (ou Famille de Context)
    private static RelationalContextFamily relCtx = null;

    // Le menu et sous menu File
    private JMenu menuFile = null;

    private JMenuItem changeCtxNameItem = null;

    private JMenuItem importItem = null;

    private JMenuItem exportItem = null;

    private JMenuItem saveAllItem = null;

    private JMenuItem closeItem = null;

    // Le menu et sous menu Edit
    private JMenu menuEdit;

    private JMenuItem showGraphItem = null;

    private JMenuItem changeRelNameItem = null;

    private JMenuItem addRelItemB = null;

    private JMenuItem addRelItemR = null;

    private JMenuItem createInterObjectRel = null;

    private JMenuItem addRelItemM = null;

    private JMenuItem deleteRelItem = null;

    private JMenuItem addObjItem = null;

    private JMenuItem addAttItem = null;

    private JMenuItem deleteObjItem = null;

    private JMenuItem deleteAttItem = null;

    private JMenuItem razItem = null;

    private JMenu scaleMenu;

    private JMenuItem nomiScaleItem;

    private JMenuItem dichoScaleItem;

    private JMenuItem specScaleItem;

    // Le menu Algo
    JMenu menuAlgo;

    // Le menu Alpha
    JMenu menuAlpha;

    // Dans le menu console
    protected JMenuItem savConsItem;

    // Le contenaire de JTable et un Vecteur les comptabilisants
    private JTabbedPane ongletPanel = null;

    private List<BinaryRelationTableEditor> setOfAbsRelTableEditor = null;

    // Un marqueur de job
    Hashtable relationOnWork = new Hashtable();

    // Popup sur JTable
    // protected JPopupMenu popupMenu = null;
    // protected JMenuItem popupChgVal = null;

    // Les controlers
    protected RuleController ruleC;

    protected LatticeController latticeC;

    protected LatticeUpdateController latticeUC;

    protected IcebergController latticeIcebergC;

    protected AlphaController alphaMergeControler;

    protected MergeController mergeC;

    protected GSHController shgC;

    protected RCAController rcaC;

    protected DatabaseController databaseC;

    /**
     * Constructor for RelationalContextEditor.
     * 
     * @throws HeadlessException
     */
    public RelationalContextEditor(RelationalContextFamily rc) {
        super(0.8d);
        relCtx = rc;

        // Initialisation de la Fenetre principale
        this.setTitle("Contexts Family Name : " + relCtx.getName());
        setSize(800, 600);
        setLocation(150, 70);
        setOfAbsRelTableEditor = new Vector();
        initComponents();
    }

    private void initComponents() {

        readTask = new ReadingTask(this);
        writeTask = new WritingTask(this);

        ruleC = new RuleController(this);
        latticeC = new LatticeController(this);
        latticeIcebergC = new IcebergController(this);

        alphaMergeControler = new AlphaController(this);
        shgC = new GSHController(this);
        latticeUC = new LatticeUpdateController(this);
        mergeC = new MergeController(this);
        rcaC = new RCAController(this);
        databaseC = new DatabaseController(this);

        // Initialise la barre de menu
        initMenuBar();

        // Initialise la vue principale
        initView();

        // Init Popup
        initPopup();

        // Init Possible Action
        checkPossibleActions();
    }

    // ---------------------------------------------------------------------------------------
    // --------------------------------- ------------------------------
    // --------------------------------- Dbu Initialisation
    // ------------------------------
    // --------------------------------- ------------------------------
    // ---------------------------------------------------------------------------------------

    private void initMenuBar() {
        // Initialise le Menu File
        initMenuFile();

        // Initialise le Menu Edition
        initMenuEdit();

        menuAlgo = new JMenu("Algorithms");
        menuAlgo.setMnemonic('A');
        menuAlgo.add(latticeC.getMainMenu());
        menuAlgo.add(latticeIcebergC.getMainMenu());
        menuAlgo.add(shgC.getMainMenu());
        menuAlgo.add(latticeUC.getMainMenu());
        menuAlgo.add(mergeC.getMainMenu());
        menuAlgo.add(rcaC.getMainMenu());

        menuAlpha = alphaMergeControler.getMainMenu();

        maBar = new JMenuBar();
        maBar.add(menuFile);
        maBar.add(menuEdit);
        maBar.add(ruleC.getMainMenu());
        maBar.add(menuAlgo);
        maBar.add(menuAlpha);
        maBar.add(databaseC.getMainMenu());

        savConsItem = new JMenuItem("Save Console");
        savConsItem.addActionListener(this);
        consoleMenu.addSeparator();
        consoleMenu.add(savConsItem);
        maBar.add(consoleMenu);

        setJMenuBar(maBar);
    }

    private void initMenuFile() {
        // Le menu
        menuFile = new JMenu("File");
        menuFile.setMnemonic('F');

        changeCtxNameItem = new JMenuItem("Change Contexts Family Name");
        changeCtxNameItem.addActionListener(this);
        changeCtxNameItem.setMnemonic('N');
        changeCtxNameItem.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_N,
                              java.awt.event.KeyEvent.CTRL_MASK, false));

        importItem = new JMenuItem("Import...");
        importItem.addActionListener(this);
        importItem.setMnemonic('I');
        importItem.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_I,
                              java.awt.event.KeyEvent.CTRL_MASK, false));

        exportItem = new JMenuItem("Export...");
        exportItem.addActionListener(this);
        exportItem.setMnemonic('E');
        exportItem.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_E,
                              java.awt.event.KeyEvent.CTRL_MASK, false));

        saveAllItem = new JMenuItem("Save All...");
        saveAllItem.addActionListener(this);
        saveAllItem.setMnemonic('S');
        saveAllItem.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_S,
                              java.awt.event.KeyEvent.CTRL_MASK
                                      | java.awt.event.KeyEvent.SHIFT_MASK,
                              false));

        closeItem = new JMenuItem("Close the Contexts Family");
        closeItem.addActionListener(this);
        closeItem.setMnemonic('Q');
        closeItem.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_Q,
                              java.awt.event.KeyEvent.CTRL_MASK, false));

        // Ajout des items
        menuFile.add(changeCtxNameItem);
        menuFile.addSeparator();
        menuFile.add(importItem);
        menuFile.add(exportItem);
        menuFile.addSeparator();
        menuFile.add(saveAllItem);
        menuFile.add(closeItem);

    }

    private void initMenuEdit() {
        // Le menu
        menuEdit = new JMenu("Edit");
        menuEdit.setMnemonic('E');

        showGraphItem = new JMenuItem("Show Associated Lattice");
        showGraphItem.addActionListener(this);
        showGraphItem.setMnemonic('S');

        changeRelNameItem = new JMenuItem("Change Context Name");
        changeRelNameItem.addActionListener(this);
        changeRelNameItem.setMnemonic('N');
        changeRelNameItem.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_N,
                              java.awt.event.KeyEvent.CTRL_MASK
                                      | java.awt.event.KeyEvent.SHIFT_MASK,
                              false));

        addRelItemB = new JMenuItem("Add a new Binary Context");
        addRelItemB.addActionListener(this);
        addRelItemB.setMnemonic('B');
        addRelItemB.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_B,
                              java.awt.event.KeyEvent.CTRL_MASK, false));
        addRelItemR = new JMenuItem("Add a new Random Binary Context");
        addRelItemR.addActionListener(this);
        addRelItemR.setMnemonic('R');
        addRelItemR.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_B,
                              java.awt.event.KeyEvent.CTRL_MASK
                                      | java.awt.event.KeyEvent.SHIFT_MASK,
                              false));

        addRelItemM = new JMenuItem("Add a new Multi-Valued Context");
        addRelItemM.addActionListener(this);
        addRelItemM.setMnemonic('M');
        addRelItemM.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_M,
                              java.awt.event.KeyEvent.CTRL_MASK, false));

        createInterObjectRel = new JMenuItem("Create an inter-object relation");
        createInterObjectRel.setMnemonic('C');
        createInterObjectRel.addActionListener(this);

        deleteRelItem = new JMenuItem("Remove the Selected Context");
        deleteRelItem.addActionListener(this);
        deleteRelItem.setMnemonic('R');
        deleteRelItem.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_R,
                              java.awt.event.KeyEvent.CTRL_MASK, false));

        addObjItem = new JMenuItem("Add an Object to Selected Context");
        addObjItem.addActionListener(this);
        addObjItem.setMnemonic('O');
        addObjItem.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_O,
                              java.awt.event.KeyEvent.CTRL_MASK, false));

        addAttItem = new JMenuItem("Add an Attribut to Selected Context");
        addAttItem.addActionListener(this);
        addAttItem.setMnemonic('A');
        addAttItem.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_A,
                              java.awt.event.KeyEvent.CTRL_MASK, false));

        deleteObjItem = new JMenuItem("Delete an Object from Selected Context");
        deleteObjItem.addActionListener(this);
        deleteObjItem.setMnemonic('O');
        deleteObjItem.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_O,
                              java.awt.event.KeyEvent.CTRL_MASK
                                      | java.awt.event.KeyEvent.SHIFT_MASK,
                              false));

        deleteAttItem = new JMenuItem(
                                      "Delete an Attribute from Selected Context");
        deleteAttItem.addActionListener(this);
        deleteAttItem.setMnemonic('A');
        deleteAttItem.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_A,
                              java.awt.event.KeyEvent.CTRL_MASK
                                      | java.awt.event.KeyEvent.SHIFT_MASK,
                              false));

        razItem = new JMenuItem("Reset Relations to Selected Context");
        razItem.addActionListener(this);
        razItem.setMnemonic('Z');
        razItem.setAccelerator(javax.swing.KeyStroke
                .getKeyStroke(java.awt.event.KeyEvent.VK_Z,
                              java.awt.event.KeyEvent.CTRL_MASK
                                      | java.awt.event.KeyEvent.SHIFT_MASK,
                              false));

        scaleMenu = new JMenu("Scalling");
        // scaleMenu.setMnemonic('S');

        nomiScaleItem = new JMenuItem("Nominale Scale");
        nomiScaleItem.addActionListener(this);
        // nomiScaleItem.setMnemonic('N');

        dichoScaleItem = new JMenuItem("Dichotomic Scale");
        dichoScaleItem.addActionListener(this);
        // dichoScaleItem.setMnemonic('D');

        specScaleItem = new JMenuItem("Specify a Scale Relation");
        specScaleItem.addActionListener(this);
        // specScaleItem.setMnemonic('S');

        menuEdit.add(showGraphItem);
        menuEdit.addSeparator();
        menuEdit.add(changeRelNameItem);
        menuEdit.addSeparator();
        menuEdit.add(addRelItemB);
        menuEdit.add(addRelItemR);
        menuEdit.add(addRelItemM);
        menuEdit.add(createInterObjectRel);
        menuEdit.add(deleteRelItem);
        menuEdit.addSeparator();
        menuEdit.add(addObjItem);
        menuEdit.add(addAttItem);
        menuEdit.add(deleteObjItem);
        menuEdit.add(deleteAttItem);
        menuEdit.add(razItem);
        menuEdit.addSeparator();
        menuEdit.add(scaleMenu);
        scaleMenu.add(nomiScaleItem);
        scaleMenu.add(dichoScaleItem);
        scaleMenu.add(specScaleItem);

    }

    private void initView() {
        ongletPanel = new JTabbedPane(JTabbedPane.TOP);
        ongletPanel.addChangeListener(this);
        // ongletPanel.setTabLayoutPolicy(JTabbedPane.SCROLL_TAB_LAYOUT);
        RelationBuilder absRel = null;
        AbstractRelationTableEditor absRelTE = null;
        AbstractRelationTableModel absRelTM = null;
        for (int i = 0; i < relCtx.size(); i++) {
            absRel = relCtx.get(i);
            if (absRel instanceof MatrixBinaryRelationBuilder) {
                showBinaryRelation((MatrixBinaryRelationBuilder) absRel);
            }
         }
        setTopPanel(ongletPanel);
    }

    private void initPopup() {
        // popupMenu = new JPopupMenu();
        // popupChgVal = new JMenuItem("Change the value...");
        // popupMenu.add(popupChgVal);
        // popupChgVal.addActionListener(this);
    }

    public void checkPossibleActions() {
        if (relCtx.size() == 0) {
            saveAllItem.setEnabled(false);
            showGraphItem.setEnabled(false);
            exportItem.setEnabled(false);
            changeRelNameItem.setEnabled(false);
            addAttItem.setEnabled(false);
            addObjItem.setEnabled(false);
            deleteAttItem.setEnabled(false);
            deleteObjItem.setEnabled(false);
            deleteRelItem.setEnabled(false);
            razItem.setEnabled(false);
            scaleMenu.setEnabled(false);
            menuAlgo.setEnabled(false);
            menuAlpha.setEnabled(false);
            ruleC.checkPossibleActions();
            latticeC.checkPossibleActions();
            latticeUC.checkPossibleActions();
            latticeIcebergC.checkPossibleActions();
            shgC.checkPossibleActions();
            mergeC.checkPossibleActions();
            rcaC.checkPossibleActions();
            databaseC.checkPossibleActions();
            return;
        }

        RelationBuilder absRel = relCtx.get(ongletPanel
                .getSelectedIndex());

        if (absRel instanceof MatrixBinaryRelationBuilder) {
            saveAllItem.setEnabled(true);
            showGraphItem.setEnabled(true);
            exportItem.setEnabled(true);
            changeRelNameItem.setEnabled(true);
            addAttItem.setEnabled(true);
            addObjItem.setEnabled(true);
            deleteAttItem.setEnabled(true);
            deleteObjItem.setEnabled(true);
            deleteRelItem.setEnabled(true);
            scaleMenu.setEnabled(false);
            menuAlgo.setEnabled(true);
            menuAlpha.setEnabled(true);
        }

        if (absRel instanceof ScalingBinaryRelation) {
            saveAllItem.setEnabled(true);
            showGraphItem.setEnabled(false);
            exportItem.setEnabled(true);
            changeRelNameItem.setEnabled(true);
            addAttItem.setEnabled(false);
            addObjItem.setEnabled(false);
            deleteAttItem.setEnabled(false);
            deleteObjItem.setEnabled(false);
            deleteRelItem.setEnabled(true);
            scaleMenu.setEnabled(false);
            menuAlgo.setEnabled(false);
            menuAlpha.setEnabled(false);
        }

        if (absRel instanceof InterObjectBinaryRelation) {
            saveAllItem.setEnabled(true);
            showGraphItem.setEnabled(false);
            exportItem.setEnabled(true);
            changeRelNameItem.setEnabled(true);
            addAttItem.setEnabled(false);
            addObjItem.setEnabled(false);
            deleteAttItem.setEnabled(false);
            deleteObjItem.setEnabled(false);
            deleteRelItem.setEnabled(true);
            scaleMenu.setEnabled(false);
            menuAlgo.setEnabled(false);
            menuAlpha.setEnabled(false);
        }

        ruleC.checkPossibleActions();
        latticeC.checkPossibleActions();
        latticeUC.checkPossibleActions();
        latticeIcebergC.checkPossibleActions();
        shgC.checkPossibleActions();
        mergeC.checkPossibleActions();
        rcaC.checkPossibleActions();
        databaseC.checkPossibleActions();

    }

    // ---------------------------------------------------------------------------------------
    // --------------------------------- ------------------------------
    // --------------------------------- Fin Initialisation
    // ------------------------------
    // ---------------------------------------------------------------------------------------
    // --------------------------------- ------------------------------
    // --------------------------------- Dbu Action Performed
    // ------------------------------
    // --------------------------------- ------------------------------
    // ---------------------------------------------------------------------------------------

    public void actionPerformed(ActionEvent ae) {
        super.actionPerformed(ae);
        String notAvailableStr = new String(
                                            "Sorry, this algorithm is not available in this version.\n");
        // ********************* Menu File
        // ***************************************************************

        if (ae.getSource() == changeCtxNameItem) {
            renameRelationalContext();
        }

        if (ae.getSource() == importItem) {
            importData();
        }

        if (ae.getSource() == exportItem) {
            exportData();
        }

        if (ae.getSource() == saveAllItem) {
            saveAllData(relCtx);
        }

        if (ae.getSource() == closeItem) {
            closeRelationalContextEditor();
        }

        // ********************* Menu Edit
        // ***************************************************************

        if (ae.getSource() == showGraphItem) {
            if (isOnWork(getSelectedRelation()))
                JOptionPane
                        .showMessageDialog(this,
                                           "You can not modify this context, it is already used through an algorithm.");
            else
                showAssociatedGraph();
        }

        if (ae.getSource() == changeRelNameItem) {
            if (isOnWork(getSelectedRelation()))
                JOptionPane
                        .showMessageDialog(this,
                                           "You can not modify this context, it is already used through an algorithm.");
            else
                renameRelation();
        }

        if (ae.getSource() == addRelItemB) {
            createNewBinaryRelation();
        }
        if (ae.getSource() == addRelItemR) {
            createNewRandomBinaryRelation();
            checkPossibleActions();
        }

        if (ae.getSource() == createInterObjectRel) {
            createInterObjectBinaryRelationTable();
            checkPossibleActions();
        }

        if (ae.getSource() == deleteRelItem) {
            if (isOnWork(getSelectedRelation()))
                JOptionPane
                        .showMessageDialog(this,
                                           "You can not modify this context, it is already used through an algorithm.");
            else
                removeRelation();
        }

        if (ae.getSource() == addObjItem) {
            if (isOnWork(getSelectedRelation()))
                JOptionPane
                        .showMessageDialog(this,
                                           "You can not modify this context, it is already used through an algorithm.");
            else
                addFormalObject();
        }

        if (ae.getSource() == addAttItem) {
            if (isOnWork(getSelectedRelation()))
                JOptionPane
                        .showMessageDialog(this,
                                           "You can not modify this context, it is already used through an algorithm.");
            else
                addFormalAttribute();
        }

        if (ae.getSource() == deleteObjItem) {
            if (isOnWork(getSelectedRelation()))
                JOptionPane
                        .showMessageDialog(this,
                                           "You can not modify this context, it is already used through an algorithm.");
            else
                removeFormalObject();
        }

        if (ae.getSource() == deleteAttItem) {
            if (isOnWork(getSelectedRelation()))
                JOptionPane
                        .showMessageDialog(this,
                                           "You can not modify this context, it is already used through an algorithm.");
            else
                removeFormalAttribute();
        }

        if (ae.getSource() == razItem) {
            if (isOnWork(getSelectedRelation()))
                JOptionPane
                        .showMessageDialog(this,
                                           "You can not modify this context, it is already used through an algorithm.");
            else
                razRelationValues();
        }

        if (ae.getSource() == dichoScaleItem) {
            execDichotomicSaling();
        }


        // ********************* Menu Console
        // ***************************************************************

        if (ae.getSource() == savConsItem) {
            addMessage("Write Console...");
            // File f=chooseAnyFile();
            // line replaced by Amine, to confirm with C�line
            File f = chooseSaveConsoleFile();
            if (f != null) {
                try {
                    ConsoleWriter cs = new ConsoleWriter(
                                                         new BufferedWriter(
                                                                            new FileWriter(
                                                                                           f)));
                    cs.setData(console);
                    writeTask.setDataWriter(cs);
                    writeTask.exec();
                } catch (Exception e) {
                    e.printStackTrace();
                    addMessage("Write Console stopped (can not create Writer)!\n");
                }
            } else {
                addMessage("Writing Console cancelled!\n");
            }
        }

        // ********************* Menu Popup
        // ***************************************************************

        // // Gestion des Item de Popup !
        // if (ae.getSource() == popupChgVal) {
        // if(isOnWork(getSelectedRelation()))
        // JOptionPane.showMessageDialog(this,"You can not modify this context,
        // it is already used through an algorithm.");
        // else doubleClickOnTableCell();
        // }

        checkPossibleActions();
    }

    // ---------------------------------------------------------------------------------------
    // --------------------------------- ------------------------------
    // --------------------------------- Fin Action Performed
    // ------------------------------
    // ---------------------------------------------------------------------------------------
    // --------------------------------- ------------------------------
    // --------------------------------- Dbu Mouse Listener
    // ------------------------------
    // --------------------------------- ------------------------------
    // ---------------------------------------------------------------------------------------

    // Gestionnaire du click souris
    public void mouseClicked(MouseEvent me) {
        // Edition lors d'un click droit
        // if (setOfAbsRelTableEditor.contains(me.getSource()) &&
        // me.getModifiers() == InputEvent.BUTTON3_MASK) {
        // AbstractRelationTableEditor
        // arte=((AbstractRelationTableEditor)setOfAbsRelTableEditor.elementAt(ongletPanel.getSelectedIndex()));
        // int rowIdx=arte.getSelectedRow();
        // int colIdx=arte.getSelectedColumn();
        //
        // if(isOnWork(getSelectedRelation()))
        // JOptionPane.showMessageDialog(this,"You can not modify this context,
        // it is already used through an algorithm.");
        // else popupMenu.show(this, ongletPanel.getX()+me.getX(),
        // ongletPanel.getY()+me.getY());
        // }

        // if (setOfAbsRelTableEditor.contains(me.getSource()) && me.getButton()
        // == MouseEvent.BUTTON1 && me.getClickCount() == 2) {
        if (setOfAbsRelTableEditor.contains(me.getSource())
            && me.getModifiers() == InputEvent.BUTTON1_MASK
            && me.getClickCount() == 2) {
            if (isOnWork(getSelectedRelation()))
                JOptionPane
                        .showMessageDialog(this,
                                           "You can not modify this context, it is already used through an algorithm.");
            else
                doubleClickOnTableCell();
        }

    }

    public void mouseEntered(MouseEvent me) {
    }

    public void mouseExited(MouseEvent me) {
    }

    public void mousePressed(MouseEvent me) {
    }

    public void mouseReleased(MouseEvent me) {
    }

    // ---------------------------------------------------------------------------------------
    // --------------------------------- ------------------------------
    // --------------------------------- Fin Mouse Listener
    // ------------------------------
    // --------------------------------- ------------------------------
    // ---------------------------------------------------------------------------------------
    // --------------------------------- ------------------------------
    // --------------------------------- Dbu Add/Del Relation
    // ------------------------------
    // --------------------------------- ------------------------------
    // ---------------------------------------------------------------------------------------

    public void addBinaryRelation(MatrixBinaryRelationBuilder binRel) {
        if (binRel == null)
            return;
        relCtx.add(binRel);
        showBinaryRelation(binRel);
    }

    public void showBinaryRelation(MatrixBinaryRelationBuilder binRel) {
        BinaryRelationTableEditor brte = new BinaryRelationTableEditor(binRel);
        brte.addMouseListener(this);
        setOfAbsRelTableEditor.add(brte);
        ongletPanel.add(binRel.getName(), new JScrollPane(brte));
        ongletPanel.setSelectedIndex(ongletPanel.getTabCount() - 1);
        ongletPanel.repaint();
    }

    public void addConceptLattice(CompleteConceptLattice cl) {
        MatrixBinaryRelationBuilder binRel = MatrixBinaryRelationBuilder.getInstanceFromLattice(cl);
        binRel.setLattice(cl);
        addBinaryRelation(binRel);
        showAssociatedGraph();
    }

    // ---------------------------------------------------------------------------------------
    // --------------------------------- ------------------------------
    // --------------------------------- Fin Add/Del Relation
    // ------------------------------
    // ---------------------------------------------------------------------------------------
    // --------------------------------- ------------------------------
    // --------------------------------- Dbu Change Listener
    // ------------------------------
    // --------------------------------- ------------------------------
    // ---------------------------------------------------------------------------------------

    public void stateChanged(ChangeEvent ce) {
        if (ce.getSource() == ongletPanel) {
            checkPossibleActions();
        }
    }

    // ---------------------------------------------------------------------------------------
    // --------------------------------- ------------------------------
    // --------------------------------- Fin Change Listener
    // ------------------------------
    // ---------------------------------------------------------------------------------------
    // --------------------------------- ------------------------------
    // --------------------------------- Dbu Specific Action
    // ------------------------------
    // --------------------------------- ------------------------------
    // ---------------------------------------------------------------------------------------

    public RelationalContextFamily getFamilyContexts() {
        return relCtx;
    }

    public RelationBuilder getSelectedRelation() {
        return (RelationBuilder) relCtx.get(ongletPanel
                .getSelectedIndex());
    }

    public AbstractRelationTableEditor getSelectedTableEditor() {
        return (AbstractRelationTableEditor) setOfAbsRelTableEditor
                .get(ongletPanel.getSelectedIndex());
    }

    // ********************* Menu File
    // ***************************************************************

    protected void renameRelationalContext() {
        String newName = JOptionPane
                .showInputDialog(this,
                                 "Give a new name for the relational context :");
        if (newName != null && !newName.equals("")) {
            relCtx.setName(newName);
            setTitle("Contexts Family name : " + newName);
        }

    }

    protected void exportData() {
        addMessage("Export...");
        // Choose
        ExportDialogSelection eds = new ExportDialogSelection(relCtx, this);
        eds.askParameter();
        if (eds.getAction() == ExportDialogSelection.CANCELLED) {
            addMessage("Export Cancelled!\n");
            return;
        }
        if (eds.getData() == null) {
            addMessage("No data to export!");
            addMessage("Export Cancelled!\n");
            return;
        } else
            writeAction(eds.getData(), "Export", eds.getTypeOfExport());

    }

    protected void closeRelationalContextEditor() {
        databaseC.closeConnection();
        this.processWindowEvent(new WindowEvent(this,
                                                WindowEvent.WINDOW_CLOSING));
    }

    // ********************* Menu Edit
    // ***************************************************************

    public void showAssociatedGraph() {
        RelationBuilder absr = relCtx.get(ongletPanel
                .getSelectedIndex());
        CompleteConceptLattice lat = absr.getLattice();
        if (lat == null) {
            JOptionPane
                    .showMessageDialog(this,
                                       "This context has no associated lattice graph.");
            return;
        } else {
            LatticeGraphFrame f = new LatticeGraphFrame(lat.getDescription(),
                                                        lat.getTop());
            f.show();
        }
    }

    protected void renameRelation() {
        String newName = JOptionPane
                .showInputDialog(this, "Give a new name for the relation :");
        if (newName != null && !newName.equals("")) {
            ongletPanel.setTitleAt(ongletPanel.getSelectedIndex(), newName);
            relCtx.get(ongletPanel.getSelectedIndex())
                    .setName(newName);
            ongletPanel.getSelectedComponent().validate();
        } else {
            addMessage("Changing relation name cancelled!\n");
        }

    }

    protected void createNewBinaryRelation() {
        addMessage("Add a new binary relation ");
        String numObjS = null;
        int numObj = 0;
        do {
            numObjS = JOptionPane.showInputDialog(this,
                                                  "Give a number of objects:");
            if (numObjS != null) {
                if (!numObjS.equals("")) {
                    try {
                        numObj = Integer.parseInt(numObjS);
                    } catch (NumberFormatException nfe) {
                        numObj = 0;
                    }
                }
                if (numObjS.equals("") || numObj <= 0)
                    JOptionPane
                            .showMessageDialog(this,
                                               "The input should be an integer >0");
            }
        } while (numObjS != null && (numObjS.equals("") || numObj <= 0));
        if (numObjS == null) {
            addMessage("Add a new binary relation canceled...\n");
            return;
        }

        String numAttS = null;
        int numAtt = 0;
        do {
            numAttS = JOptionPane
                    .showInputDialog(this, "Give a number of attributes :");
            if (numAttS != null) {
                if (!numAttS.equals("")) {
                    try {
                        numAtt = Integer.parseInt(numAttS);
                    } catch (NumberFormatException nfe) {
                        numAtt = 0;
                    }
                }
                if (numAttS.equals("") || numAtt <= 0) {
                    JOptionPane
                            .showMessageDialog(this,
                                               "Give a number of attributes :");
                }
            }
        } while (numAttS != null && (numAttS.equals("") || numAtt <= 0));
        if (numAttS == null) {
            addMessage("Add a new binary relation canceled...\n");
            return;
        }

        MatrixBinaryRelationBuilder binRel = new MatrixBinaryRelationBuilder(numObj, numAtt);
        addBinaryRelation(binRel);
        addMessage("Add a new binary relation completed\n");
    }

    protected void createNewRandomBinaryRelation() {
        String numObjS = null;
        int numObj = 0;
        do {
            numObjS = JOptionPane.showInputDialog(this,
                                                  "Give a number of objects :");
            if (numObjS != null) {
                if (!numObjS.equals("")) {
                    try {
                        numObj = Integer.parseInt(numObjS);
                    } catch (NumberFormatException nfe) {
                        numObj = 0;
                    }
                }
                if (numObjS.equals("") || numObj <= 0)
                    JOptionPane
                            .showMessageDialog(this,
                                               "The input should be an integer >0");
            }
        } while (numObjS != null && (numObjS.equals("") || numObj <= 0));
        if (numObjS == null) {
            addMessage("Add a new random binary relation canceled...\n");
            return;
        }

        String numAttS = null;
        int numAtt = 0;
        do {
            numAttS = JOptionPane
                    .showInputDialog(this, "Give a number of attributes :");
            if (numAttS != null) {
                if (!numAttS.equals("")) {
                    try {
                        numAtt = Integer.parseInt(numAttS);
                    } catch (NumberFormatException nfe) {
                        numAtt = 0;
                    }
                }
                if (numAttS.equals("") || numAtt <= 0) {
                    JOptionPane
                            .showMessageDialog(this,
                                               "Give a number of attributes :");
                }
            }
        } while (numAttS != null && (numAttS.equals("") || numAtt <= 0));
        if (numAttS == null) {
            addMessage("Add a new random binary relation canceled...\n");
            return;
        }

        String densiteS = null;
        int densite = 0;
        do {
            densiteS = JOptionPane
                    .showInputDialog(this, "Give the context density :");
            if (densiteS != null) {
                if (!densiteS.equals("")) {
                    try {
                        densite = Integer.parseInt(densiteS);
                    } catch (NumberFormatException nfe) {
                        densite = 0;
                    }
                }
                if (densiteS.equals("") || numAtt <= 0) {
                    JOptionPane.showMessageDialog(this,
                                                  "Give the context density :");
                }
            }
        } while (densiteS != null && (densiteS.equals("") || densite <= 0));
        if (densiteS == null) {
            addMessage("Add a new random binary relation canceled...\n");
            return;
        }

        MatrixBinaryRelationBuilder binRel = new MatrixBinaryRelationBuilder(numObj, numAtt);
        int nbElt = binRel.randomBinaryRelation(densite);
        addBinaryRelation(binRel);
        addMessage("New random binary relation completed with " + nbElt
                   + " relations\n");
    }

    public void removeRelation() {
        if (relCtx.size() == 0)
            return;
        addMessage("Remove a relation: started");
        int idx = ongletPanel.getSelectedIndex();
        relCtx.remove(idx);
        setOfAbsRelTableEditor.remove(idx);
        ongletPanel.remove(idx);
        checkPossibleActions();
        addMessage("Remove a relation: completed\n");
    }

    protected void addFormalObject() {
        int relIdx = ongletPanel.getSelectedIndex();
        RelationBuilder absRel = relCtx.get(relIdx);
        absRel.addObject();
        ((AbstractRelationTableEditor) setOfAbsRelTableEditor
                .get(ongletPanel.getSelectedIndex()))
                .setModelFromRelation(absRel);
        ongletPanel.getSelectedComponent().validate();
    }

    protected void addFormalAttribute() {
        int relIdx = ongletPanel.getSelectedIndex();
        RelationBuilder absRel = relCtx.get(relIdx);
        absRel.addAttribute();
        ((AbstractRelationTableEditor) setOfAbsRelTableEditor
                .get(ongletPanel.getSelectedIndex()))
                .setModelFromRelation(absRel);
        ongletPanel.getSelectedComponent().validate();
    }

    protected void removeFormalObject() {
        int relIdx = ongletPanel.getSelectedIndex();
        RelationBuilder absRel = relCtx.get(relIdx);
        FormalObject[] lesVals = absRel.getFormalObjects();
        FormalObject fo = (FormalObject) JOptionPane
                .showInputDialog(this, "Remove an object",
                                 "Choose an object to remove :",
                                 JOptionPane.QUESTION_MESSAGE, null, lesVals,
                                 lesVals[0]);
        if (fo != null) {
            absRel.removeObject(fo);
        }
        ((AbstractRelationTableEditor) setOfAbsRelTableEditor
                .get(ongletPanel.getSelectedIndex()))
                .setModelFromRelation(absRel);
        ongletPanel.getSelectedComponent().validate();
    }

    protected void removeFormalAttribute() {
        int relIdx = ongletPanel.getSelectedIndex();
        RelationBuilder absRel = relCtx.get(relIdx);
        FormalAttribute[] lesVals = absRel.getFormalAttributes();
        if (lesVals == null) {
            System.out.println("lesVals == null");
        }
        FormalAttribute temp = lesVals[0];
        FormalAttribute fa = (FormalAttribute) JOptionPane
                .showInputDialog(this, "Remove an attribute",
                                 "Choose an attribute to remove :",
                                 JOptionPane.QUESTION_MESSAGE, null, lesVals,
                                 temp);
        if (fa != null) {
            absRel.removeAttribute(fa);
        }
        ((AbstractRelationTableEditor) setOfAbsRelTableEditor
                .get(ongletPanel.getSelectedIndex()))
                .setModelFromRelation(absRel);
        ongletPanel.getSelectedComponent().validate();
    }

    protected void doubleClickOnTableCell() {
        AbstractRelationTableEditor arte = ((AbstractRelationTableEditor) setOfAbsRelTableEditor
                .get(ongletPanel.getSelectedIndex()));
        int rowIdx = arte.getSelectedRow();
        int colIdx = arte.getSelectedColumn();
        if (rowIdx == 0 && colIdx == 0) {
            renameRelation();
        }
        if (rowIdx == 0
            && colIdx > 0
            && !(relCtx.get(ongletPanel.getSelectedIndex()) instanceof ScalingBinaryRelation)
            && !(relCtx.get(ongletPanel.getSelectedIndex()) instanceof InterObjectBinaryRelation)) {
            String val = null;
            do {
                val = JOptionPane
                        .showInputDialog(this, "Give a name to formal attribut"
                                               + arte
                                                       .getValueAt(rowIdx,
                                                                   colIdx));
                if (val != null) {
                    if (val.equals("") || val.indexOf("|") != -1) {
                        JOptionPane
                                .showMessageDialog(this,
                                                   "The name shouldn't be empty and shouldn't contains any '|' character.");
                    } else {
                        arte.getModel().setValueAt(val, rowIdx, colIdx);
                    }
                }
            } while (val != null && (val.equals("") | val.indexOf("|") != -1));
            if (val == null) {
                addMessage("Changing formal attribute name cancelled!\n");
            }
        }
        if (rowIdx > 0
            && colIdx == 0
            && !(relCtx.get(ongletPanel.getSelectedIndex()) instanceof ScalingBinaryRelation)
            && !(relCtx.get(ongletPanel.getSelectedIndex()) instanceof InterObjectBinaryRelation)) {
            String val = null;
            do {
                val = JOptionPane
                        .showInputDialog(this, "Give a name to formal object"
                                               + arte
                                                       .getValueAt(rowIdx,
                                                                   colIdx));
                if (val != null) {
                    if (val.equals("") || val.indexOf("|") != -1) {
                        JOptionPane
                                .showMessageDialog(this,
                                                   "The name shouldn't be empty and shouldn't contains any '|' character.");
                    } else {
                        arte.getModel().setValueAt(val, rowIdx, colIdx);
                    }
                }
            } while (val != null && (val.equals("") | val.indexOf("|") != -1));
            if (val == null) {
                addMessage("Changing formal object name cancelled!\n");
            }
        }
        if (rowIdx > 0 && colIdx > 0) {
            arte.queryNewInputRelationValue(rowIdx, colIdx);
        }
    }

    protected void razRelationValues() {
        addMessage("Reset Relation");
        relCtx.get(ongletPanel.getSelectedIndex()).emptyRelation();
        addMessage("Done!\n");
        // addMessage("This option is not yet imlemented!\n");
    }

    protected void execDichotomicSaling() {
        addMessage("This scalling is not yet imlemented!\n");
    }


    public void createInterObjectBinaryRelationTable() {

        String relAttrName = JOptionPane
                .showInputDialog(this,
                                 "What is the name of the relational attribute: ");
        List<String> relNames = new ArrayList<String>();
        for (int i = 0; i < relCtx.size(); i++) {
            if (relCtx.get(i) instanceof InterObjectBinaryRelation)
                continue;
            if (relCtx.get(i) instanceof ScalingBinaryRelation)
                continue;
            if (relCtx.get(i) instanceof MatrixBinaryRelationBuilder)
                relNames.add(relCtx.get(i).getName());
        }// for
        if (relNames.size() == 0) {
            addMessage("There is no binary or many-valed relation in the family...!\n");
            return;
        }
        String sourceCtx = (String) JOptionPane
                .showInputDialog(
                                 this,
                                 "Choose a source context for the relational attribute: ",
                                 "Source context :",
                                 JOptionPane.QUESTION_MESSAGE, null, relNames
                                         .toArray(), relNames.get(0));
        if (sourceCtx == null)
            return;
        String targetCtx = (String) JOptionPane
                .showInputDialog(
                                 this,
                                 "Choose a target context for the relational attribute: ",
                                 "Target context :",
                                 JOptionPane.QUESTION_MESSAGE, null, relNames
                                         .toArray(), relNames.get(0));
        if (targetCtx == null)
            return;
        RelationBuilder sourceRel = relCtx.getForName(sourceCtx);
        RelationBuilder targetRel = relCtx.getForName(targetCtx);
        InterObjectBinaryRelation newRel = new InterObjectBinaryRelation(
                                                                         sourceRel,
                                                                         targetRel);
        newRel.setName(relAttrName);
        addBinaryRelation(newRel);

    }

    public void setWorkOnRelation(RelationBuilder absr) {
        relationOnWork.put(absr, new Integer(1));
    }

    public void releaseWorkOnRelation(RelationBuilder absr) {
        relationOnWork.remove(absr);
    }

    public boolean isOnWork(RelationBuilder absr) {
        return (relationOnWork.get(absr) != null);
    }

    // ---------------------------------------------------------------------------------------
    // --------------------------------- ------------------------------
    // --------------------------------- Fin Specific Action
    // ------------------------------
    // --------------------------------- ------------------------------
    // ---------------------------------------------------------------------------------------
    // --------------------------------- ------------------------------
    // --------------------------------- Dbu Window Listener
    // ------------------------------
    // --------------------------------- ------------------------------
    // ---------------------------------------------------------------------------------------
    /*
     * (non-Javadoc)
     * 
     * @see java.awt.event.WindowListener#windowActivated(java.awt.event.WindowEvent)
     */
    public void windowActivated(WindowEvent arg0) {
        // TODO Auto-generated method stub

    }

    /*
     * (non-Javadoc)
     * 
     * @see java.awt.event.WindowListener#windowClosed(java.awt.event.WindowEvent)
     */
    public void windowClosing(WindowEvent arg0) {
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.awt.event.WindowListener#windowClosing(java.awt.event.WindowEvent)
     */
    public void windowClosed(WindowEvent arg0) {
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.awt.event.WindowListener#windowDeactivated(java.awt.event.WindowEvent)
     */
    public void windowDeactivated(WindowEvent arg0) {
        // TODO Auto-generated method stub

    }

    /*
     * (non-Javadoc)
     * 
     * @see java.awt.event.WindowListener#windowDeiconified(java.awt.event.WindowEvent)
     */
    public void windowDeiconified(WindowEvent arg0) {
        // TODO Auto-generated method stub

    }

    /*
     * (non-Javadoc)
     * 
     * @see java.awt.event.WindowListener#windowIconified(java.awt.event.WindowEvent)
     */
    public void windowIconified(WindowEvent arg0) {
        // TODO Auto-generated method stub

    }

    /*
     * (non-Javadoc)
     * 
     * @see java.awt.event.WindowListener#windowOpened(java.awt.event.WindowEvent)
     */
    public void windowOpened(WindowEvent arg0) {
        // TODO Auto-generated method stub

    }

    // ---------------------------------------------------------------------------------------
    // --------------------------------- ------------------------------
    // --------------------------------- Fin Window Listener
    // ------------------------------
    // --------------------------------- ------------------------------
    // ---------------------------------------------------------------------------------------

    public void showTaskResult(Object theResult) {

        for (int i = 0; theResult instanceof AbstractTask
                        && i < ((AbstractTask) theResult).getBinRelOnUse()
                                .size(); i++) {
            // lorsque qu'une tache se d�roule comme les algo il ne faut pas
            // lancer
            // 2 algo sur les m�me relation binaire donc les relation soncerne
            // sont marqu�s
            // quand l'algo a terminer il faut donc relacher les marqueur
            releaseWorkOnRelation(((AbstractTask) theResult).getBinRelOnUse()
                    .get(i));
        }

        if (theResult instanceof LatticeAlgorithmTask) {
            // Le calcul d'un trellis viens de se terminer il faut l'afficher !
            LatticeAlgorithm algo = (LatticeAlgorithm) ((LatticeAlgorithmTask) theResult)
                    .getAlgo();

            if (algo instanceof Gagci_NoInc) {
                for (int i = 0; i < ((Gagci_NoInc) algo)
                        .getSetOfEnrichingRelations().size(); i++) {
                    String title = ((MatrixBinaryRelationBuilder) ((Gagci_NoInc) algo)
                            .getSetOfEnrichingRelations().elementAt(i))
                            .getName();
                    LatticeGraphFrame f = new LatticeGraphFrame(
                                                                title,
                                                                ((MatrixBinaryRelationBuilder) ((Gagci_NoInc) algo)
                                                                        .getSetOfEnrichingRelations()
                                                                        .elementAt(
                                                                                   i))
                                                                        .getLattice()
                                                                        .getTop());
                    f.show();
                }
            } else {
                LatticeGraphFrame f = new LatticeGraphFrame(algo
                        .getDescription(), algo.getLattice().getTop());
                f.show();
            }
        }

        if (theResult instanceof ruleAbstractTask) {
            console.addMessage(((ruleAbstractTask) theResult).getResultat());
        }

        if (theResult instanceof ReadingTask) {
            addMessage("rce: taskResult is a ReadingTask");
            Object theData = ((ReadingTask) theResult).getData();
            if (theData instanceof MatrixBinaryRelationBuilder) {
                addMessage("rce: theData is a MatrixBinaryRelationBuilder");
                if (((MatrixBinaryRelationBuilder) theData).getName()
                        .equals(RelationBuilder.DEFAULT_NAME)) {
                    ((MatrixBinaryRelationBuilder) theData)
                            .setName(((ReadingTask) theResult)
                                    .getDefaultNameForData());
                }
                if (relCtx.getName()
                        .equals(RelationalContextFamily.DEFAULT_NAME)) {
                    relCtx.setName(((ReadingTask) theResult)
                            .getDefaultNameForData());
                    setTitle("Contexts Family name: "
                             + ((ReadingTask) theResult)
                                     .getDefaultNameForData());
                }
                addBinaryRelation((MatrixBinaryRelationBuilder) theData);
                addMessage("Reading done!\n");
            }

            if (theData instanceof RelationalContextFamily) {
                RelationalContextFamily rc = (RelationalContextFamily) theData;
                addMessage("rce: theData is a RelationalContextFamily with "
                           + rc.size() + " relations");
                if (relCtx.getName()
                        .equals(RelationalContextFamily.DEFAULT_NAME)) {
                    relCtx.setName(((ReadingTask) theResult)
                            .getDefaultNameForData());
                    setTitle("Contexts Family name: "
                             + ((ReadingTask) theResult)
                                     .getDefaultNameForData());
                }
                for (int i = 0; i < rc.size(); i++) {
                    if (rc.get(i) instanceof MatrixBinaryRelationBuilder)
                        addBinaryRelation((MatrixBinaryRelationBuilder) rc.get(i));
                }
                addMessage("Reading done!\n");
            }

            if (theData instanceof CompleteConceptLattice) {
                addMessage("rce: theData is a CompleteConceptLattice");
                addConceptLattice((CompleteConceptLattice) theData);
                if (getSelectedRelation().getName()
                        .equals(RelationBuilder.DEFAULT_NAME)) {
                    getSelectedRelation()
                            .setName(
                                             ((ReadingTask) theResult)
                                                     .getDefaultNameForData());
                    ongletPanel.setTitleAt(ongletPanel.getSelectedIndex(),
                                           ((ReadingTask) theResult)
                                                   .getDefaultNameForData());
                }
                if (relCtx.getName()
                        .equals(RelationalContextFamily.DEFAULT_NAME)) {
                    relCtx.setName(((ReadingTask) theResult)
                            .getDefaultNameForData());
                    setTitle("Contexts Family name: "
                             + ((ReadingTask) theResult)
                                     .getDefaultNameForData());
                }
                addMessage("Reading done!\n");
            }
        }

        if (theResult instanceof DatabaseReadingTask) {
            Object theData = ((DatabaseReadingTask) theResult).getData();

            // Relational Context Family

            if (theData instanceof RelationalContextFamily) {

                RelationalContextFamily relCtxFam = (RelationalContextFamily) theData;
                if (relCtx.getName()
                        .equals(RelationalContextFamily.DEFAULT_NAME)) {
                    relCtx.setName(((DatabaseReadingTask) theResult)
                            .getDefaultNameForData());
                    setTitle("Contexts Family Name: "
                             + ((DatabaseReadingTask) theResult)
                                     .getDefaultNameForData());
                }

                for (int i = 0; i < relCtxFam.size(); i++) {
                    if (relCtxFam.get(i) instanceof ScalingBinaryRelation) {
                        addBinaryRelation((ScalingBinaryRelation) relCtxFam
                                .get(i));
                        addMessage("Relation '"
                                   + relCtxFam.get(i).getName()
                                   + "' loaded from database");
                    } else if (relCtxFam.get(i) instanceof InterObjectBinaryRelation) {
                        addBinaryRelation((InterObjectBinaryRelation) relCtxFam
                                .get(i));
                        addMessage("Relation '"
                                   + relCtxFam.get(i).getName()
                                   + "' loaded from database");
                    } else if (relCtxFam.get(i) instanceof MatrixBinaryRelationBuilder) {
                        addBinaryRelation((MatrixBinaryRelationBuilder) relCtxFam
                                .get(i));
                        addMessage("Relation '"
                                   + relCtxFam.get(i).getName()
                                   + "' loaded from database");
                    } 
                }
                addMessage("Reading from database done\n");
            }

            // Rules Basis

            else if (theData instanceof RulesBasis) {
                String dataName = ((DatabaseReadingTask) theResult)
                        .getDefaultNameForData();

                if (dataName.equals("View Rules Basis")) {
                    addMessage("Viewing rules basis...");
                    RulesBasis rulesBasis = (RulesBasis) theData;
                    if (theData != null) {
                        new TableVisualization(rulesBasis, this);
                    }
                    addMessage("Rules basis successfully loaded\n");
                } else if (dataName.equals("Export Rules Basis")) {
                    addMessage("Exporting rules basis...");
                    RulesBasis rulesBasis = (RulesBasis) theData;
                    if (theData != null) {
                        JFileChooser chooser = new JFileChooser();
                        chooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
                        chooser.setMultiSelectionEnabled(false);
                        chooser.setFileFilter(new XML_Filter(""));
                        chooser.setDialogTitle("Select the Output File");

                        if (chooser.showSaveDialog(null) == JFileChooser.APPROVE_OPTION) {

                            String fileName = chooser.getSelectedFile()
                                    .getAbsolutePath();
                            if (!fileName.substring(fileName.length() - 4,
                                                    fileName.length())
                                    .equals(".xml")) {
                                fileName += ".xml";
                            }
                            Set<Rule> rules = rulesBasis.getRules();
                            boolean isExact = true;
                            Iterator<Rule> ruleIter = rules.iterator();
                            while (ruleIter.hasNext() && isExact) {
                                if (ruleIter.next().getConfiance() < 1.00) {
                                    isExact = false;
                                }
                            }
                           XmlRuleExport export = new XmlRuleExport();
                            if (isExact) {
                                export.sauvegardeReglesExactesFichierXML(
                                                                           fileName,
                                                                           rules,
                                                                           rulesBasis
                                                                                   .getDatasetName(),
                                                                           rulesBasis
                                                                                   .getMinConfidence(),
                                                                           rulesBasis
                                                                                   .getMinSupport());
                            } else {
                                export
                                        .sauvegardeReglesApproximativesFichierXML(
                                                                                  fileName,
                                                                                  rules,
                                                                                  rulesBasis
                                                                                          .getDatasetName(),
                                                                                  rulesBasis
                                                                                          .getMinConfidence(),
                                                                                  rulesBasis
                                                                                          .getMinSupport());
                            }
                        }
                    }
                    addMessage("Rules basis successfully exported\n");
                }
            }

            // Lattices

            else if (theData instanceof CompleteConceptLattice) {
                String dataName = ((DatabaseReadingTask) theResult)
                        .getDefaultNameForData();

                if (dataName.equals("View Lattice")) {
                    addMessage("Viewing lattice...");
                    CompleteConceptLattice lattice = (CompleteConceptLattice) theData;
                    if (lattice != null) {
                        getSelectedRelation().setLattice(lattice);
                        new LatticeGraphFrame(lattice.getDescription(), lattice
                                .getTop()).show();
                    }
                    addMessage("Lattice successfully loaded\n");
                } else if (dataName.equals("Export Lattice")) {
                    addMessage("Exporting lattice...");
                    CompleteConceptLattice lattice = (CompleteConceptLattice) theData;
                    if (lattice != null) {
                        JFileChooser chooser = new JFileChooser();
                        chooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
                        chooser.setMultiSelectionEnabled(false);
                        chooser.setFileFilter(new XML_Filter(".lat"));
                        chooser.setDialogTitle("Select the Output File");

                        if (chooser.showSaveDialog(null) == JFileChooser.APPROVE_OPTION) {
                            String fileName = chooser.getSelectedFile()
                                    .getAbsolutePath();
                            if (!fileName.substring(fileName.length() - 8,
                                                    fileName.length())
                                    .equals(".lat.xml")) {
                                fileName += ".lat.xml";
                            }
                            try {
                                XmlWriter writer = new XmlWriter(
                                                                 new FileWriter(
                                                                                fileName));
                                writer.writeConceptLattice(lattice);
                            } catch (Exception e) {
                                DatabaseFunctions
                                        .showMessageDialog("Exportation failed");
                                addMessage("Exportation failed\n");
                            }
                        }
                    }
                    addMessage("Lattice successfully exported\n");
                }
            }
        }

        else if (theResult instanceof DatabaseWritingTask) {
            Object theData = ((DatabaseWritingTask) theResult).getData();

            if (theData instanceof Vector) {
                Vector relations = (Vector) theData;
                for (int i = 0; i < relations.size(); i++) {
                    addMessage("Relation '" + relations.get(i)
                               + "' saved to the database");
                }
                DatabaseFunctions
                        .showMessageDialog("Relations saved to the database");
            } else if (theData instanceof RulesBasis) {
                addMessage("Rules Basis '"
                           + ((RulesBasis) theData).getDatasetName()
                           + "' saved to the database");
                DatabaseFunctions
                        .showMessageDialog("Rules Basis saved to the database");
            } else if (theData instanceof String) {
                addMessage("Lattice associated to '" + theData
                           + "' saved to database");
                DatabaseFunctions
                        .showMessageDialog("Lattice saved to the database");
            }
            addMessage("Saving to database done\n");
        }

        if (theResult instanceof String) {
            addMessage(theResult.toString());
        }

        checkPossibleActions();
    }

    public Concept removeAttribute() {
        Concept concept = null;
        Intent intent = new SetIntent();
        Extent extent = new SetExtent();

        int relIdx = ongletPanel.getSelectedIndex();
        RelationBuilder absRel = relCtx.get(relIdx);
        FormalAttribute[] lesVals = absRel.getFormalAttributes();
        if (lesVals == null) {
            System.out.println("lesVals == null");
        }
        FormalAttribute temp = lesVals[0];
        FormalAttribute fa = (FormalAttribute) JOptionPane
                .showInputDialog(this, "Remove an attribute",
                                 "Choose an attribute to remove :",
                                 JOptionPane.QUESTION_MESSAGE, null, lesVals,
                                 temp);
        if (fa != null) {
            intent.add(fa);
            int idxA = absRel.getAttributes().indexOf(fa);
            for (int i = 0; i < absRel.getObjectsNumber(); i++) {
                String str = absRel.getRelation(i, idxA).toString();
                if (str.equals("X")) {
                    FormalObject fo = absRel.getObjects().get(i);
                    extent.add(fo);
                }
            }
            concept = new ConceptImp(extent, intent);
            absRel.removeAttribute(fa);
        }
        ((AbstractRelationTableEditor) setOfAbsRelTableEditor
                .get(ongletPanel.getSelectedIndex()))
                .setModelFromRelation(absRel);
        ongletPanel.getSelectedComponent().validate();
        // System.out.println("CONCEPT: "+concept.getExtent()+" ,
        // "+concept.getIntent());
        return (concept);
    }

    public static RelationalContextFamily getRCF() {
        return relCtx;
    }
}
