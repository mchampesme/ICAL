/*
 *  Copyright LIPN
 *  contributor(s) : Marc Champesme (2006) marc.champesme@lipn.univ-paris13.fr
 *  
 *  This software is a computer program whose purpose is the Incremental construction of Alpha lattices.
 *  
 *  This software is governed by the CeCILL license under French law and
 *  abiding by the rules of distribution of free software.  You can  use, 
 *  modify and/ or redistribute the software under the terms of the CeCILL
 *  license as circulated by CEA, CNRS and INRIA at the following URL
 *  "http://www.cecill.info". 
 *  
 *  As a counterpart to the access to the source code and  rights to copy,
 *  modify and redistribute granted by the license, users are provided only
 *  with a limited warranty  and the software's author,  the holder of the
 *  economic rights,  and the successive licensors  have only  limited
 *  liability. 
 *  
 *  In this respect, the user's attention is drawn to the risks associated
 *  with loading,  using,  modifying and/or developing or reproducing the
 *  software by the user in light of its specific status of free software,
 *  that may mean  that it is complicated to manipulate,  and  that  also
 *  therefore means  that it is reserved for developers  and  experienced
 *  professionals having in-depth computer knowledge. Users are therefore
 *  encouraged to load and test the software's suitability as regards their
 *  requirements in conditions enabling the security of their systems and/or 
 *  data to be ensured and,  more generally, to use and operate it in the 
 *  same conditions as regards security. 
 *  
 *  The fact that you are presently reading this means that you have had
 *  knowledge of the CeCILL license and that you accept its terms.
 */
package lattice.alpha.gui.controller;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.event.ActionEvent;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPanel;

import lattice.algorithm.LatticeAlgorithm;
import lattice.algorithm.task.LatticeAlgorithmTask;
import lattice.alpha.algorithm.merge.MergeAlpha;
import lattice.alpha.gui.LatticeAsTreeBrowser;
import lattice.alpha.gui.controller.dialog.ChoiceDialogSelectionAlpha;
import lattice.alpha.gui.model.LatticeModel;
import lattice.alpha.gui.model.LatticeTableModel;
import lattice.alpha.gui.model.RelationModel;
import lattice.alpha.gui.model.RelationTableModel;
import lattice.alpha.gui.view.LatticeSelectionPanel;
import lattice.alpha.gui.view.PercentTextFieldPanel;
import lattice.alpha.gui.view.RelationSelectionPanel;
import lattice.alpha.iceberg.algorithm.BordatLatticeBuilder;
import lattice.alpha.rules.generator.Jen;
import lattice.alpha.util.BitSetExtent;
import lattice.alpha.util.BitSetIntent;
import lattice.gui.RelationalContextEditor;
import lattice.gui.controller.AbstractController;
import lattice.gui.graph.LatticeGraphFrame;
import lattice.util.concept.AbstractFormalAttributeValue;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.relation.ScalingBinaryRelation;
import lattice.util.structure.CompleteConceptLattice;
import orderedset.ArrayHashSet;
import orderedset.ImmutIndexedSet;
import rule.algorithm.GenericBasis;
import rule.algorithm.InformativeBasis;
import rule.gui.TableVisualization;
import rule.util.RulesBasis;

/**
 * cette class permet de controler la fusion des treillis fr�quents, elle permet
 * l'interaction avec l'utilisateur
 * 
 * @author eljaouhari
 * @author Marc Champesme
 */
public class AlphaController extends AbstractController implements PropertyChangeListener {

    public final static String SHOW_ALPHA_WINDOW_CMD = "Show Alpha Window";
    public final static String SHOW_ALPHA_WINDOW_CMD_MSG = "Show Alpha Window";
    
    public final static String BROWSE_LATTICE_CMD = "Browse Lattice";
    public final static String SHOW_LATTICE_CMD = "Show Lattice";
    public final static String BUILD_LATTICE_CMD = "Build Lattices";
    public final static String GENERATOR_CMD = "Compute Generators";
    public final static String MERGE_CMD = "Merge Lattices";
    public final static String GENERIC_BASIS_CMD = "Compute Generic Basis";
    public final static String INFORMATIVE_BASIS_CMD = "Compute Informative Basis";
    
    public final static String BUILD_LATTICE_CMD_MSG = "Build Lattices";
    public final static String GENERATOR_CMD_MSG = "Generators";
    public final static String GENERIC_BASIS_CMD_MSG = "Generic Basis";
    public final static String INFORMATIVE_BASIS_CMD_MSG = "Informative Basis";
    public final static String MERGE_CMD_MSG = "Merge";
    public final static String BROWSE_LATTICE_CMD_MSG = "Browse Lattice";
    public final static String SHOW_LATTICE_CMD_MSG = "Show Lattice";
    
    private JFrame alphaWindow;
    private JButton generatorButton;
    private JButton genericBasisButton;
    private JButton informativeBasisButton;
    private JButton mergeButton;
    private JButton buildLatticeButton;
    private JButton browseLatticeButton;
    private JButton showLatticeButton;

    private LatticeTableModel latticeTable;
    
    private LatticeSelectionPanel latticeSelectionPanel;
    
    private RelationTableModel relationTable;
    
    private RelationSelectionPanel relationSelectionPanel;

    // Numerical parameters:
    private double alphaValue;
    private PercentTextFieldPanel alphaTextField;
    
    private double minSupport;
    private PercentTextFieldPanel minSupportTextField;
    
    private double minConfidence;
    private PercentTextFieldPanel minConfidenceTextField;
    
    
    private JMenu alphaMenu;
    
    private JMenuItem showAlphaWindow;

    private JMenu paramsMenu;
    private JMenu buildMenu;
    private JMenu viewMenu;

    private JMenuItem alphaValueMenuItem;

    private JMenuItem minSupportMenuItem;
    private JMenuItem minConfidenceMenuItem;

    private JCheckBoxMenuItem showLatticeParamsMenuItem;

    private JCheckBoxMenuItem showLatticeResultMenuItem;

    private JMenuItem viewLatticeMenuItem;
    private JMenuItem viewExactBRMenuItem;
    private JMenuItem viewApproxBRMenuItem;

    private JMenuItem latticeBuilderMenuItem;
    private JMenuItem generatorMenuItem;
    private JMenuItem exactBRMenuItem;
    private JMenuItem approxBRMenuItem;

    private LatticeAlgorithmTask theTask;

    private boolean showLatticeParams;

    private boolean showLatticeResult;

    private Object[] paramArray;

    private List<CompleteConceptLattice> latticeParamList;

    private List<CompleteConceptLattice> resultList;

    private List<RelationBuilder> relationList;

    private List<Extent> classList;
    private Map<RelationBuilder, BitSetExtent> relationToClassMap;
    
    private Map<FormalObject, Intent> objToIntentMap;
    
    private ImmutIndexedSet<FormalAttribute> globalIntentDomain;
    
    private ImmutIndexedSet<FormalObject> globalExtentDomain;

    private List<CompleteConceptLattice> latticeList;
    
    private List<RulesBasis> exactBRList;
    
    private List<RulesBasis> approxBRList;


    /**
     * cre�tion du controleur
     * 
     * @param rce
     */
    public AlphaController(RelationalContextEditor rce) {
        super(rce);
        alphaValue = 0.6;
        minSupport = 0.3;
        minConfidence = 0.4;
        RelationalContextFamily rcf = rce.getFamilyContexts();
        int nbRelations = rcf.size();
        latticeParamList = new ArrayList<CompleteConceptLattice>(nbRelations);
        resultList = new ArrayList<CompleteConceptLattice>(nbRelations);
        relationList = new ArrayList<RelationBuilder>(nbRelations);
        classList = new ArrayList<Extent>(nbRelations);
        relationToClassMap = new HashMap<RelationBuilder, BitSetExtent>(nbRelations * 4 / 3);
        latticeList = new ArrayList<CompleteConceptLattice>(nbRelations);
        latticeTable = new LatticeTableModel();
        relationTable = new RelationTableModel();
        exactBRList = new ArrayList<RulesBasis>();
        approxBRList = new ArrayList<RulesBasis>();
        showLatticeParams = false;
        showLatticeResult = false;
        initMenu();
        theTask = new LatticeAlgorithmTask(rce);
    }

    private void initAlphaWindow() {
        //Make sure we have nice window decorations.
        JFrame.setDefaultLookAndFeelDecorated(true);

        //Create and set up the window.
        alphaWindow = new JFrame("Alpha Lattices");
        JPanel contentPane = new JPanel(new BorderLayout(10, 10));

        JPanel textFieldPane = new JPanel();
        alphaTextField = new PercentTextFieldPanel("Alpha Value:", alphaValue);
        alphaTextField.addValueChangeListener(this);
        minSupportTextField = new PercentTextFieldPanel("Minimal Support for rules:", minSupport);
        minSupportTextField.addValueChangeListener(this);
        minConfidenceTextField = new PercentTextFieldPanel("Minimal Confidence for rules:", minConfidence);
        minConfidenceTextField.addValueChangeListener(this);
        textFieldPane.add(alphaTextField);
        textFieldPane.add(minSupportTextField);
        textFieldPane.add(minConfidenceTextField);
        contentPane.add(textFieldPane, BorderLayout.PAGE_START);

        JPanel relationPanel = new JPanel(new BorderLayout(10, 10));
        relationPanel.setBorder(BorderFactory.createEmptyBorder(20, 20, 20, 5));
        relationSelectionPanel = new RelationSelectionPanel("Select one or more relations:", relationTable);
        relationPanel.add(relationSelectionPanel, BorderLayout.PAGE_START);
        buildLatticeButton = new JButton(BUILD_LATTICE_CMD_MSG);
        buildLatticeButton.setActionCommand(BUILD_LATTICE_CMD);
        relationPanel.add(buildLatticeButton, BorderLayout.PAGE_END);        
        //contentPane.add(relationSelectionPanel,BorderLayout.LINE_START);
        contentPane.add(relationPanel, BorderLayout.LINE_START);
         

        JPanel latticePanel = new JPanel(new BorderLayout(10, 10));
        latticePanel.setBorder(BorderFactory.createEmptyBorder(20, 5, 20, 20));
        latticeSelectionPanel = new LatticeSelectionPanel("Select one or more lattices:", latticeTable);
        //contentPane.add(latticeSelectionPanel, BorderLayout.CENTER);
        latticePanel.add(latticeSelectionPanel, BorderLayout.PAGE_START);

        // Set the south panel: the buttons
        JPanel buttonsPanel = new JPanel();
        //southPanel.setBorder(BorderFactory.createEmptyBorder(20, 20, 20, 20));
        
        browseLatticeButton = new JButton(BROWSE_LATTICE_CMD_MSG);
        buttonsPanel.add(browseLatticeButton);
        browseLatticeButton.setActionCommand(BROWSE_LATTICE_CMD);
        showLatticeButton = new JButton(SHOW_LATTICE_CMD_MSG);
        buttonsPanel.add(showLatticeButton);
        showLatticeButton.setActionCommand(SHOW_LATTICE_CMD);
        mergeButton = new JButton(MERGE_CMD_MSG);
        buttonsPanel.add(mergeButton);
        mergeButton.setActionCommand(MERGE_CMD);
        generatorButton = new JButton(GENERATOR_CMD_MSG);
        buttonsPanel.add(generatorButton);
        generatorButton.setActionCommand(GENERATOR_CMD);
        genericBasisButton = new JButton(GENERIC_BASIS_CMD_MSG);
        buttonsPanel.add(genericBasisButton);
        genericBasisButton.setActionCommand(GENERIC_BASIS_CMD);
        informativeBasisButton = new JButton(INFORMATIVE_BASIS_CMD_MSG);
        buttonsPanel.add(informativeBasisButton);
        informativeBasisButton.setActionCommand(INFORMATIVE_BASIS_CMD);
        latticePanel.add(buttonsPanel, BorderLayout.PAGE_END);
        contentPane.add(latticePanel, BorderLayout.LINE_END);
        
        generatorButton.addActionListener(this);
        genericBasisButton.addActionListener(this);
        informativeBasisButton.addActionListener(this);
        mergeButton.addActionListener(this);
        buildLatticeButton.addActionListener(this);
        browseLatticeButton.addActionListener(this);
        showLatticeButton.addActionListener(this);
        
        contentPane.setOpaque(true); //content panes must be opaque
        alphaWindow.setContentPane(contentPane);

        //Display the window.
        alphaWindow.pack();
        alphaWindow.setVisible(true);

    }
    public void initMenu() {

        alphaMenu = new JMenu("Alpha");
        showAlphaWindow = new JMenuItem(SHOW_ALPHA_WINDOW_CMD_MSG);
        showAlphaWindow.setActionCommand(SHOW_ALPHA_WINDOW_CMD);
        showAlphaWindow.addActionListener(this);
        alphaMenu.add(showAlphaWindow);
        
        paramsMenu = new JMenu("Parameters");
        alphaMenu.add(paramsMenu);
        buildMenu = new JMenu("Algorithms");
        alphaMenu.add(buildMenu);
        viewMenu = new JMenu("Results");
        alphaMenu.add(viewMenu);

        // Les Items
        alphaValueMenuItem = new JMenuItem("Set Alpha Value");
        alphaValueMenuItem.addActionListener(this);
        paramsMenu.add(alphaValueMenuItem);

        minSupportMenuItem = new JMenuItem("Set Minimal Support");
        minSupportMenuItem.addActionListener(this);
        paramsMenu.add(minSupportMenuItem);

        minConfidenceMenuItem = new JMenuItem("Set Minimal Confidence");
        minConfidenceMenuItem.addActionListener(this);
        paramsMenu.add(minConfidenceMenuItem);

        showLatticeParamsMenuItem = new JCheckBoxMenuItem(
                                                          "Show Merged Lattices",
                                                          showLatticeParams);
        showLatticeParamsMenuItem.addActionListener(this);
        paramsMenu.add(showLatticeParamsMenuItem);

        showLatticeResultMenuItem = new JCheckBoxMenuItem(
                                                          "Show Resulting Lattice",
                                                          showLatticeResult);
        showLatticeResultMenuItem.addActionListener(this);
        paramsMenu.add(showLatticeResultMenuItem);

        viewLatticeMenuItem = new JMenuItem("View Lattices...");
        viewLatticeMenuItem.addActionListener(this);
        viewMenu.add(viewLatticeMenuItem);

        viewExactBRMenuItem = new JMenuItem("View Generic Rule Basis...");
        viewExactBRMenuItem.addActionListener(this);
        viewMenu.add(viewExactBRMenuItem);

        viewApproxBRMenuItem = new JMenuItem("View Informative Rule Basis...");
        viewApproxBRMenuItem.addActionListener(this);
        viewMenu.add(viewApproxBRMenuItem);

        latticeBuilderMenuItem = new JMenuItem("Build Lattice(s)...");
        latticeBuilderMenuItem.addActionListener(this);
        buildMenu.add(latticeBuilderMenuItem);

        generatorMenuItem = new JMenuItem("Compute Generators...");
        generatorMenuItem.addActionListener(this);
        buildMenu.add(generatorMenuItem);
        
        exactBRMenuItem = new JMenuItem("Build Generic Rule Basis...");
        exactBRMenuItem.addActionListener(this);
        buildMenu.add(exactBRMenuItem);
        
        approxBRMenuItem = new JMenuItem("Build Informative Rule Basis...");
        approxBRMenuItem.addActionListener(this);
        buildMenu.add(approxBRMenuItem);

    }

    public JMenu getMainMenu() {
        return alphaMenu;
    }

    /**
     * Open a dialog to allow the user to enter a double value
     * in the specified range.
     * 
     * @param valueDescription A text description of the value to enter
     * @param minValue The minimal value allowed
     * @param maxValue The maxiaml value allowed
     * @param previousValue The previous value of the parameter for which the user 
     * has to give a value
     *
     * @return The value entered by the user if this value is valid (i.e. a double in the specified range) ;
     * else the previous value.
     */
    /*@
      @ requires valueDescription != null;
      @ requires minValue <= previousValue && previousValue <= maxValue;
      @ ensures minValue <= \result && \result <= maxValue;
      @ pure
      @*/
    public double askDoubleInRange(String paramDescription, double minValue, double maxValue, double previousValue) {
        Component parentComponent = getRelationalContextEditor();
        double retValue = previousValue;
        boolean badValue;
        String numString = null;
        do {
            badValue = false;
            numString = JOptionPane
                    .showInputDialog(parentComponent,
                                     "Give a value for " + paramDescription, 
                                     String.valueOf(retValue));
            if (numString != null) {
                if (!numString.equals("")) {
                    try {
                        retValue = Double.parseDouble(numString);
                    } catch (NumberFormatException nfe) {
                        badValue = true;
                    }
                }
                if (badValue || numString.equals("") || retValue < minValue || retValue > maxValue) {
                    badValue = true;
                    JOptionPane
                            .showMessageDialog(parentComponent,
                                               "The input should be : " 
                                    + minValue + " <= " + paramDescription + " <= " + maxValue);
                }
             }
            } while (numString != null && badValue);
        if (numString != null) {
            return retValue;
        }
        
        return previousValue;
    }


    public void setRelationsAsClasses() {
        RelationalContextEditor relContextEditor = getRelationalContextEditor();
        RelationalContextFamily rc = relContextEditor.getFamilyContexts();
        Set<FormalObject> objectSet = new HashSet<FormalObject>(2500);
        Set<FormalAttribute> attributeSet = new HashSet<FormalAttribute>(500);
        for (int i = 0; i < rc.size(); i++) {
            RelationBuilder relation = rc.get(i);
            relationList.add(relation);
            relationTable.addRelation(relation);
            objectSet.addAll(relation.getObjects());
            attributeSet.addAll(relation.getAttributes());
        }
        globalIntentDomain = new ArrayHashSet<FormalAttribute>(attributeSet);
        globalExtentDomain = new ArrayHashSet<FormalObject>(objectSet);
        objToIntentMap = new HashMap<FormalObject, Intent>(globalExtentDomain.size() * 4 / 3);
        for (int i = 0; i < rc.size(); i++) {
            RelationBuilder relation = rc.get(i);
            BitSetExtent currentObjSet;
            currentObjSet = new BitSetExtent(globalExtentDomain, relation.getObjects());
            classList.add(currentObjSet);
            relationToClassMap.put(relation, currentObjSet);
            makeObjToIntentMap((MatrixBinaryRelationBuilder) relation, currentObjSet);
        }
    }


    public void askParamList(String msg, List<Object> selectionList) {
        Component parentComponent;

        parentComponent = getRelationalContextEditor();
        ChoiceDialogSelectionAlpha paramsSelectDialog = new ChoiceDialogSelectionAlpha(parentComponent,
                                                                                       selectionList,
                                                                                       msg);
        paramsSelectDialog.askParameter();
        if (paramsSelectDialog.getAction() == ChoiceDialogSelectionAlpha.SELECT) {
            paramArray = (Object[]) paramsSelectDialog.getData();
        } else {
            paramArray = null;
        }
    }

    public void askMergeParams() {
        List<Object> selectionList;

        selectionList = new ArrayList<Object>(relationList);
        selectionList.addAll(latticeList);
        askParamList("Select the classes/lattices you want to merge:",
                     selectionList);
    }


    public void askLatticeList(String msg) {
        List<Object> selectionList;

        selectionList = new ArrayList<Object>(latticeList);
        askParamList(msg, selectionList);
        latticeParamList.clear();
        if (paramArray != null) {
            for (int i = 0; i < paramArray.length; i++) {
                latticeParamList.add((CompleteConceptLattice) paramArray[i]);
            }
        }
    }

    public List<RulesBasis> askBRList(String msg, List<RulesBasis> ruleBaseList) {
        List<Object> selectionList;
        List<RulesBasis> selectedList;

        selectionList = new ArrayList<Object>(ruleBaseList);
        askParamList(msg, selectionList);
        selectedList = new LinkedList<RulesBasis>();
        if (paramArray != null) {
            for (int i = 0; i < paramArray.length; i++) {
                selectedList.add((RulesBasis) paramArray[i]);
            }
        }
        return selectedList;
    }

    public void prepareLatticeParams() {
        latticeParamList.clear();
        for (int i = 0; i < paramArray.length; i++) {
            Object param = paramArray[i];
            CompleteConceptLattice latticeParam = null;
            if (param instanceof MatrixBinaryRelationBuilder) {
                MatrixBinaryRelationBuilder relation = (MatrixBinaryRelationBuilder) param;
                LatticeAlgorithm algo = new BordatLatticeBuilder(relation, alphaValue, 
                                                                 objToIntentMap, 
                                                                 (BitSetExtent) relationToClassMap.get(relation), globalIntentDomain);
                algo.doAlgorithm();
                latticeParam = algo.getLattice();
                latticeParam.setDescription(relation.getName() + "("
                                            + alphaValue + ")");
                latticeList.add(latticeParam);
                latticeTable.addLattice(latticeParam, alphaValue);
                latticeParamList.add(latticeParam);
            } else {
                if (param instanceof CompleteConceptLattice) {
                    latticeParam = (CompleteConceptLattice) param;
                    latticeParamList.add(latticeParam);
                } else {
                    System.out.println("prepareLatticeParams: param is not a MatrixBinaryRelationBuilder nor a CompleteConceptLattice:" + param);
                }
            }
        }
    }

    public void browseLattice(final String windowTitle, final CompleteConceptLattice lattice) {
        //Schedule a job for the event-dispatching thread:
        //creating and showing this application's GUI.
        javax.swing.SwingUtilities.invokeLater(new Runnable() {
            public void run() {
                LatticeAsTreeBrowser.createAndShowGUI(windowTitle + ": " + lattice.getDescription(), lattice.getTop());
            }
        });
    }
    public void showLattice(String windowTitle, CompleteConceptLattice lattice) {
        LatticeGraphFrame frame;
        frame = new LatticeGraphFrame(windowTitle + ": " + lattice.getDescription(),
                                      lattice.getTop());
        frame.setVisible(true);
    }
    
    public void showRuleBasis(RulesBasis ruleBasis) {
        JFrame  ruleVisu = new TableVisualization(ruleBasis, rce);
        ruleVisu.setVisible(true);
    }

    public void computeGenerators(CompleteConceptLattice lattice) {
        System.out.println("Computing generators:");
        Jen algoGenerateurs = new Jen(lattice);
        algoGenerateurs.computeLatticeGenerators();
        System.out.println("Generators computation done.");        
    }
    
    public RulesBasis buildExactRuleList(CompleteConceptLattice lattice) {
        GenericBasis basis = new GenericBasis(lattice, 1);
        basis.doAlgorithm();
        return new RulesBasis(relationList.get(0), lattice.getDescription(), basis.getBase(), minSupport, 1);
    }
    
    public RulesBasis buildApproxRuleList(CompleteConceptLattice lattice) {
        InformativeBasis basis = new InformativeBasis(lattice, minConfidence);
        basis.doAlgorithm();
        return new RulesBasis(relationList.get(0), lattice.getDescription(), basis.getBase(), minSupport, minConfidence);
    }
    public void showLatticeList(String windowTitle, List<CompleteConceptLattice> lattices) {
         int latNumber = 1;
        for (CompleteConceptLattice lat : lattices) {
            showLattice(windowTitle + "#" + latNumber + ":", lat);
            browseLattice(windowTitle + "#" + latNumber + ":", lat);
            latNumber++;
        }
    }

    public void performMultipleMerge() {
        CompleteConceptLattice lastResult;
        CompleteConceptLattice currentLattice;
        CompleteConceptLattice resultLattice;

        Iterator<CompleteConceptLattice> iterLattice = latticeParamList.iterator();
        resultList.clear();
        if (latticeParamList.isEmpty()) {
            System.out.println("Error:latticeParamList is empty");
            return;
        }
        lastResult = iterLattice.next();
        while (iterLattice.hasNext()) {
            currentLattice = iterLattice.next();

            resultLattice = MergeAlpha.fusionne(classList, lastResult,
                                                currentLattice, alphaValue,
                                                false);
            resultLattice.setDescription(lastResult.getDescription() + "+"
                                         + currentLattice.getDescription());
            //latticeList.add(resultLattice);
            //latticeTable.addLattice(resultLattice, alphaValue);
            //resultList.add(resultLattice);
            lastResult = resultLattice;
        }
        latticeList.add(lastResult);
        latticeTable.addLattice(lastResult, alphaValue);
        resultList.add(lastResult);
    }

    /**
     * gestion des evenement
     * 
     * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
     *      
     */
    public void actionPerformed(ActionEvent event) {
        if (event.getActionCommand().equals(SHOW_ALPHA_WINDOW_CMD)) {
            if (relationTable.getRowCount() == 0) {
                setRelationsAsClasses();
                relationTable.fireTableDataChanged();
            }
            if (alphaWindow == null) {
                initAlphaWindow();
            } else {
                alphaWindow.setVisible(true);
            }
        }
        if (event.getSource() == alphaValueMenuItem) {
            alphaValue = askDoubleInRange("the alpha parameter", 0.0d, 1.0d, alphaValue);
        }
        if (event.getSource() == minSupportMenuItem) {
            minSupport = askDoubleInRange("the minimal support of rules", 0.0d, 1.0d, minSupport);
        }
        if (event.getSource() == alphaValueMenuItem) {
            minConfidence = askDoubleInRange("the minimal confidence of rules", 0.0d, 1.0d, minConfidence);
        }
        // showLatticeParamsMenuItem
        if (event.getSource() == showLatticeParamsMenuItem) {
            showLatticeParams = showLatticeParamsMenuItem.isSelected();
        }
        if (event.getSource() == showLatticeResultMenuItem) {
            showLatticeResult = showLatticeResultMenuItem.isSelected();
        }
        // viewLatticeMenuItem
        if (event.getSource() == viewLatticeMenuItem) {
            askLatticeList("Select the lattices you want to view:");
            if (latticeParamList == null || latticeParamList.isEmpty()) {
                addMessage("Nothing to show");
                return;
            }
            showLatticeList("Lattice", latticeParamList);
            latticeParamList.clear();
        }
        if (event.getSource() == viewExactBRMenuItem) {
            List<RulesBasis> selectedBR = askBRList("Select the Generic Basis you want to view", exactBRList);
            for (RulesBasis base : selectedBR) {
                showRuleBasis(base);
            }
        }
        if (event.getSource() == viewApproxBRMenuItem) {
            List<RulesBasis> selectedBR = askBRList("Select the Informative Basis you want to view", approxBRList);
            for (RulesBasis base : selectedBR) {
                showRuleBasis(base);
            }
        }
        if (event.getSource() == generatorMenuItem) {
            askLatticeList("Select the lattices for generator computation:");
            if (latticeParamList == null || latticeParamList.isEmpty()) {
                addMessage("Nothing to show");
                return;
            }
            for (CompleteConceptLattice lattice : latticeParamList) {
                computeGenerators(lattice);
            }
            latticeParamList.clear();
            addMessage("Generator computation done.");
        }
        // browse Lattice command
        if (event.getActionCommand().equals(BROWSE_LATTICE_CMD)) {
            List<LatticeModel> latticeModelList = latticeSelectionPanel.getSelectedLattices();
            if (latticeModelList == null || latticeModelList.isEmpty()) {
                addMessage("Nothing to show");
                return;
            }
            for (LatticeModel latticeModel : latticeModelList) {
            	browseLattice("Lattice",  latticeModel.getLattice());
            }
            latticeModelList.clear();
        }
        // show Lattice command
        if (event.getActionCommand().equals(SHOW_LATTICE_CMD)) {
            List<LatticeModel> latticeModelList = latticeSelectionPanel.getSelectedLattices();
            if (latticeModelList == null || latticeModelList.isEmpty()) {
                addMessage("Nothing to show");
                return;
            }
            for (LatticeModel latticeModel : latticeModelList) {
            	showLattice("Lattice",  latticeModel.getLattice());
            }
            latticeModelList.clear();
        }
        
        if (event.getActionCommand().equals(GENERATOR_CMD)) {
            List<LatticeModel> latticeModelList = latticeSelectionPanel.getSelectedLattices();
            if (latticeModelList == null || latticeModelList.isEmpty()) {
                addMessage("Nothing to show");
                return;
            }
            for (LatticeModel latticeModel : latticeModelList) {
                computeGenerators(latticeModel.getLattice());
                latticeModel.setHasGenerators();
            }
            latticeTable.fireTableDataChanged();
            latticeModelList.clear();
            addMessage("Generator computation done.");
            
        }
        if (event.getSource() == exactBRMenuItem) {
            askLatticeList("Select the lattices for Generic Basis extraction:");
            if (latticeParamList == null || latticeParamList.isEmpty()) {
                addMessage("Nothing to do");
                return;
            }
            
            for (CompleteConceptLattice lattice : latticeParamList) {
                exactBRList.add(buildExactRuleList(lattice));
            }
            latticeParamList.clear();
            addMessage("Generic Basis computation done.");            
        }
        if (event.getActionCommand() == GENERIC_BASIS_CMD) {
            List<LatticeModel> latticeModelList = latticeSelectionPanel.getSelectedLattices();
            if (latticeModelList == null || latticeModelList.isEmpty()) {
                addMessage("Nothing to show");
                return;
            }
            
            for (LatticeModel latticeModel : latticeModelList) {
                RulesBasis currentBR;
                currentBR = buildExactRuleList(latticeModel.getLattice());
                showRuleBasis(currentBR);
                exactBRList.add(currentBR);
            }
            latticeModelList.clear();
            addMessage("Generic Basis computation done.");            
        }
        if (event.getSource() == approxBRMenuItem) {
            askLatticeList("Select the lattices for Informative Basis extraction:");
            if (latticeParamList == null || latticeParamList.isEmpty()) {
                addMessage("Nothing to do");
                return;
            }
            
            for (CompleteConceptLattice lattice : latticeParamList) {
                approxBRList.add(buildApproxRuleList(lattice));
            }
            latticeParamList.clear();
            addMessage("Informative Basis computation done.");            
            
        }
        if (event.getActionCommand().equals(INFORMATIVE_BASIS_CMD)) {
            List<LatticeModel> latticeModelList = latticeSelectionPanel.getSelectedLattices();
            if (latticeModelList == null || latticeModelList.isEmpty()) {
                addMessage("Nothing to show");
                return;
            }
            
            for (LatticeModel latticeModel : latticeModelList) {
                RulesBasis currentBR;
                currentBR = buildApproxRuleList(latticeModel.getLattice());
                showRuleBasis(currentBR);
                approxBRList.add(currentBR);
            }
            latticeModelList.clear();
            addMessage("Generic Basis computation done.");            
        }
        if (event.getActionCommand().equals(MERGE_CMD)) {
            List<LatticeModel> latticeModelList = latticeSelectionPanel.getSelectedLattices();
            if (latticeModelList == null || latticeModelList.size() < 2) {
                addMessage("Incorrect parameters");
                return;
            }
            
            latticeParamList.clear();
            for (LatticeModel latticeModel : latticeModelList) {
                latticeParamList.add(latticeModel.getLattice());
            }
            performMultipleMerge();
            latticeParamList.clear();
            addMessage("Merging done.");
        }
        if (event.getActionCommand().equals(BUILD_LATTICE_CMD)) {
            List<RelationModel> relationList = relationSelectionPanel.getSelectedRelations();
            if (relationList == null || relationList.isEmpty()) {
                addMessage("Incorrect parameters");
                return;
            }
            
            for (RelationModel relationModel : relationList) {
                MatrixBinaryRelationBuilder relation = (MatrixBinaryRelationBuilder) relationModel.getRelation();
                LatticeAlgorithm algo = new BordatLatticeBuilder(relation, alphaValue, 
                                                                 objToIntentMap, 
                                                                 relationToClassMap.get(relation), 
                                                                 globalIntentDomain);
                algo.doAlgorithm();
                CompleteConceptLattice latticeParam = algo.getLattice();
                latticeParam.setDescription(relation.getName() + "("
                                                + alphaValue + ")");
                latticeList.add(latticeParam);
                latticeTable.addLattice(latticeParam, alphaValue);
                latticeParamList.add(latticeParam);
            }
            addMessage("Lattice Building done.");
        }

        if (event.getSource() == latticeBuilderMenuItem) {
            if (relationList.isEmpty()) {
                setRelationsAsClasses();
                if (relationList.isEmpty()) {
                    addMessage("Classes are not defined");
                    addMessage("Algorithm \"BordatIcebergAlpha\" canceled !\n");
                    return;
                }
            }

            askMergeParams();
            if (paramArray == null || paramArray.length < 2) {
                addMessage("Invalid merge parameters");
                addMessage("Algorithm \"BordatIcebergAlpha\" canceled !\n");
                return;
            }
            prepareLatticeParams();
            if (latticeParamList == null || latticeParamList.size() < 2) {
                addMessage("Invalid merge lattice parameters");
                addMessage("Algorithm \"BordatIcebergAlpha\" canceled !\n");
                return;
            }

            performMultipleMerge();
            if (showLatticeParams) {
                showLatticeList("Param", latticeParamList);
            }
            if (showLatticeResult) {
                showLatticeList("Result", resultList);
            }
        }
        paramArray = null;
        latticeParamList.clear();
        resultList.clear();
        rce.checkPossibleActions();
    }

    protected void execAlgorithm(LatticeAlgorithm algo) {
        rce.setWorkOnRelation(algo.getBinaryRelation()); // marquer la
        // relation 'On Use'
        List<MatrixBinaryRelationBuilder> binRelOnUse = new ArrayList<MatrixBinaryRelationBuilder>();
        binRelOnUse.add(algo.getBinaryRelation());
        theTask.setBinRelOnUse(binRelOnUse);
        theTask.setAlgo(algo);
        theTask.exec();
    }

    public void checkPossibleActions() {

        if (rce.getFamilyContexts().size() == 0) {
            alphaMenu.setEnabled(false);
            return;
        }

        RelationBuilder absRel = rce.getSelectedRelation();

        if (absRel instanceof MatrixBinaryRelationBuilder) {
            alphaMenu.setEnabled(true);
            if (rce.isOnWork(absRel))
                alphaMenu.setEnabled(false);
            return;
        }

        if (absRel instanceof ScalingBinaryRelation) {
            alphaMenu.setEnabled(false);
            return;
        }

        if (absRel instanceof InterObjectBinaryRelation) {
            alphaMenu.setEnabled(false);
            return;
        }
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        if (alphaTextField.isSourceOfPropertyChange(e)) {
            alphaValue = alphaTextField.getValue();
        } else if (minSupportTextField.isSourceOfPropertyChange(e)) {
            minSupport = minSupportTextField.getValue();
        } else if (minConfidenceTextField.isSourceOfPropertyChange(e)) {
            minConfidence = minConfidenceTextField.getValue();
        }
    }
    

    public void makeObjToIntentMap(MatrixBinaryRelationBuilder relation, Set<FormalObject> objectSet) {
        for (FormalObject currentObject : objectSet) {
            BitSetIntent intent = new BitSetIntent(globalIntentDomain);
            
            for (FormalAttribute currentAttribute : globalIntentDomain) {
                AbstractFormalAttributeValue relValue = relation.getRelation(currentObject, currentAttribute);
                if(!relValue.isFalse()) {
                    intent.fastAdd(currentAttribute);
                }
            }
            objToIntentMap.put(currentObject, intent);
        }
    }

}
