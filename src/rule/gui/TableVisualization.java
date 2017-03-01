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
package rule.gui;

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Point;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.table.AbstractTableModel;

import lattice.database.gui.DatabaseConfiguration;
import lattice.database.util.DatabaseFunctions;
import lattice.database.util.DatabaseManagement;
import lattice.gui.RelationalContextEditor;
import lattice.gui.filter.XML_Filter;
import rule.io.XmlRuleExport;
import rule.util.Rule;
import rule.util.RulesBasis;

/**
 * A Swing GUI to visualize rules basis in a table
 * @author Manuel Aupetit
 */
public class TableVisualization extends JFrame {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 276937887896891429L;
	private RulesBasis rulesBasis = null;
	private List<Rule> ruleList;
	private RelationalContextEditor relCtxEd = null;
	public static Point location = new Point(60, 40);

	// Chart Visualization Values
	public static int imageWidth = 800;
	public static int imageHeight = 600;
	public static int windowWidth = 800;
	public static int windowHeight = 600;
	public static int preferredMarginWidth = 100;
	public static int preferredMarginHeight = 150;
	public static int barChartHeightRatio = 1;
	public static int attributesChartHeightRatio = 2;
	
	private javax.swing.JPanel jContentPane = null;
	
	private JPanel bottomPanel = null;
	private JPanel mainPanel = null;
	private JPanel filterButtonsPanel = null;
	private JButton premiseFilterButton = null;
	private JButton consequenceFilterButton = null;
	private JButton supportFilterButton = null;
	private JButton confidenceFilterButton = null;
	private JTable table = null;
	private JScrollPane rulesBasisScrollPane = null;
	
	private JPanel validationPanel = null;
	private JButton databaseButton = null;
	private JButton xmlButton = null;
	private JButton viewChartButton = null;
	private JPanel connectPanel = null;
	private JButton connectButton = null;
	private JPanel informationPanel = null;
	private JLabel relNameLabel = null;
	private JLabel nbRelLabel = null;
	private JLabel minSupportLabel = null;
	private JLabel maxSupportLabel = null;
	private JLabel minConfidenceLabel = null;
	private JLabel maxConfidenceLabel = null;
	/**
	 * 
	 * @param rulesBasis
	 * @param relCtxEd
	 */
	public TableVisualization(RulesBasis rulesBasis, RelationalContextEditor relCtxEd) {
		super();
		this.relCtxEd = relCtxEd;
		if (rulesBasis.getRules() != null && !rulesBasis.getRules().isEmpty()) {
			this.rulesBasis = rulesBasis;
			this.ruleList = new ArrayList<Rule>(rulesBasis.getRules());
			if (rulesBasis.getDatasetName() == null) {
				String datasetName = "";
				while (datasetName.equals("")) {
					datasetName = DatabaseFunctions.showInputDialog("Enter the dataset name:", "dataset");
					if (datasetName == null) break;
				}
				if (datasetName != null) {
					this.rulesBasis.setDatasetName(datasetName);
					initialize();
				}
			} else {
				initialize();
			}
		} else {
			DatabaseFunctions.showMessageDialog("No rules generated");
		}
	}
	
	/**
	 * This method initializes this	
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setTitle("Rules Basis Table Visualization [Dataset '" + rulesBasis.getDatasetName() + "']");
		this.setSize(800, 600);
		this.setLocation(location);
		location = new Point(location.x+20, location.y+20);
		this.setContentPane(getJContentPane());
		this.setVisible(true);	
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
	}
	
	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private javax.swing.JPanel getJContentPane() {
		if(jContentPane == null) {
			jContentPane = new javax.swing.JPanel();
			jContentPane.setLayout(new java.awt.BorderLayout());
			jContentPane.add(getMainPanel(), java.awt.BorderLayout.CENTER);
			jContentPane.add(getBottomPanel(), java.awt.BorderLayout.SOUTH);
		}
		return jContentPane;
	}
	/**
	 * This method initializes bottomPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */    
	private JPanel getBottomPanel() {
		if (bottomPanel == null) {
			bottomPanel = new JPanel();
			bottomPanel.setLayout(new BorderLayout());
			bottomPanel.add(getInformationPanel(), java.awt.BorderLayout.NORTH);
			bottomPanel.add(getConnectPanel(), java.awt.BorderLayout.WEST);
			bottomPanel.add(getValidationPanel(), java.awt.BorderLayout.EAST);
		}
		return bottomPanel;
	}
	/**
	 * This method initializes mainPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */    
	private JPanel getMainPanel() {
		if (mainPanel == null) {
			mainPanel = new JPanel();
			mainPanel.setLayout(new BorderLayout());
			mainPanel.add(getFilterButtonsPanel(), java.awt.BorderLayout.NORTH);
			mainPanel.add(getRulesBasisScrollPane(), java.awt.BorderLayout.CENTER);
		}
		return mainPanel;
	}
	/**
	 * This method initializes filterButtonsPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */    
	private JPanel getFilterButtonsPanel() {
		if (filterButtonsPanel == null) {
			java.awt.GridBagConstraints gridBagConstraints6 = new GridBagConstraints();
			java.awt.GridBagConstraints gridBagConstraints5 = new GridBagConstraints();
			java.awt.GridBagConstraints gridBagConstraints4 = new GridBagConstraints();
			java.awt.GridBagConstraints gridBagConstraints3 = new GridBagConstraints();
			filterButtonsPanel = new JPanel();
			filterButtonsPanel.setLayout(new GridBagLayout());
			gridBagConstraints3.gridx = 1;
			gridBagConstraints3.weightx = 1.0D;
			gridBagConstraints3.insets = new java.awt.Insets(20,15,10,15);
			gridBagConstraints4.gridx = 2;
			gridBagConstraints4.weightx = 1.0D;
			gridBagConstraints4.insets = new java.awt.Insets(20,15,10,15);
			gridBagConstraints5.gridx = 3;
			gridBagConstraints5.weightx = 0.0D;
			gridBagConstraints5.insets = new java.awt.Insets(20,15,10,15);
			gridBagConstraints6.gridx = 4;
			gridBagConstraints6.weightx = 0.0D;
			gridBagConstraints6.insets = new java.awt.Insets(20,15,10,30);
			filterButtonsPanel.add(getPremiseFilterButton(), gridBagConstraints3);
			filterButtonsPanel.add(getConsequenceFilterButton(), gridBagConstraints4);
			filterButtonsPanel.add(getSupportFilterButton(), gridBagConstraints5);
			filterButtonsPanel.add(getConfidenceFilterButton(), gridBagConstraints6);
		}
		return filterButtonsPanel;
	}
	/**
	 * This method initializes premiseFilterButton	
	 * 	
	 * @return javax.swing.JButton	
	 */    
	private JButton getPremiseFilterButton() {
		if (premiseFilterButton == null) {
			premiseFilterButton = new JButton();
			premiseFilterButton.setText("Filter...");
			premiseFilterButton.addActionListener(new java.awt.event.ActionListener() { 
				public void actionPerformed(java.awt.event.ActionEvent e) {
					new AttributesFilter(rulesBasis, AttributesFilter.PREMISE_MODE, relCtxEd);
				}
			});
		}
		return premiseFilterButton;
	}
	/**
	 * This method initializes consequenceFilterButton	
	 * 	
	 * @return javax.swing.JButton	
	 */    
	private JButton getConsequenceFilterButton() {
		if (consequenceFilterButton == null) {
			consequenceFilterButton = new JButton();
			consequenceFilterButton.setText("Filter...");
			consequenceFilterButton.addActionListener(new java.awt.event.ActionListener() { 
				public void actionPerformed(java.awt.event.ActionEvent e) {    
					new AttributesFilter(rulesBasis, AttributesFilter.CONSEQUENCE_MODE, relCtxEd);
				}
			});
		}
		return consequenceFilterButton;
	}
	/**
	 * This method initializes supportFilterButton	
	 * 	
	 * @return javax.swing.JButton	
	 */    
	private JButton getSupportFilterButton() {
		if (supportFilterButton == null) {
			supportFilterButton = new JButton();
			supportFilterButton.setText("Filter...");
			supportFilterButton.addActionListener(new java.awt.event.ActionListener() {   
				public void actionPerformed(java.awt.event.ActionEvent e) {
					new ExtremumFilter(rulesBasis, ExtremumFilter.RULES_BASIS_SUPPORT_MODE, relCtxEd);
				} 
				
			});
		}
		return supportFilterButton;
	}
	/**
	 * This method initializes confidenceFilterButton	
	 * 	
	 * @return javax.swing.JButton	
	 */    
	private JButton getConfidenceFilterButton() {
		if (confidenceFilterButton == null) {
			confidenceFilterButton = new JButton();
			confidenceFilterButton.setText("Filter...");
			confidenceFilterButton.addActionListener(new java.awt.event.ActionListener() {   
				public void actionPerformed(java.awt.event.ActionEvent e) {    
					new ExtremumFilter(rulesBasis, ExtremumFilter.RULES_BASIS_CONFIDENCE_MODE, relCtxEd);
				} 
			});
		}
		return confidenceFilterButton;
	}
	/**
	 * This method initializes rulesBasisScrollPane	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */    
	private JScrollPane getRulesBasisScrollPane() {
		if (rulesBasisScrollPane == null) {
			rulesBasisScrollPane = new JScrollPane();
			rulesBasisScrollPane.setViewportView(getRulesBasisTable());
			rulesBasisScrollPane.setHorizontalScrollBarPolicy(javax.swing.JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);
			rulesBasisScrollPane.setVerticalScrollBarPolicy(javax.swing.JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
		}
		return rulesBasisScrollPane;
	}
	
	
	/**
	 * 
	 * @author Manuel Aupetit
	 *
	 */
	class RulesTableModel extends AbstractTableModel {
		
		public final String[] columnNames = {"Premise", "Consequence", "Support", "Confidence"};
		private Object[][] rulesValues;
		
		public RulesTableModel() {
			setRulesValues();
		}
		
		public void setRulesValues() {
			this.rulesValues = new Object[rulesBasis.getNbRules()][4];
			Iterator<Rule> ruleIter = rulesBasis.getRules().iterator();
			for (int row=0; row<rulesBasis.getNbRules() && ruleIter.hasNext(); row++) {
				Rule tempRule = ruleIter.next();
				rulesValues[row][0] = tempRule.getAntecedent().toString();
				rulesValues[row][1] = tempRule.getConsequence().toString();
				rulesValues[row][2] = new Double(((int)(tempRule.getSupport()*100))/100.0);
				rulesValues[row][3] = new Double(((int)(tempRule.getConfiance()*100))/100.0);
			}
		}
		
		public int getRowCount() {
			return rulesValues.length;
		}
		
		public int getColumnCount() {
			return rulesValues[0].length;
		} 
		
		public Object getValueAt(int row, int column) {
			return rulesValues[row][column];
		} 
		
		public String getColumnName(int column) {
			return columnNames[column];
		}
	}
	
	
	/**
	 * This method initializes rulesBasisTable	
	 * 	
	 * @return javax.swing.JTable	
	 */    
	private JTable getRulesBasisTable() {
		if (table == null) {
			TableSorter rulesSorter = new TableSorter(new RulesTableModel());
			table = new JTable(rulesSorter);
			
			table.getTableHeader().setReorderingAllowed(false);
			table.getTableHeader().setResizingAllowed(false);
			
			AttributesColumnRenderer attRenderer = new AttributesColumnRenderer();
			NumericColumnRenderer numRenderer = new NumericColumnRenderer();
			table.getColumnModel().getColumn(0).setCellRenderer(attRenderer);
			table.getColumnModel().getColumn(0).setMinWidth(100);
			table.getColumnModel().getColumn(1).setCellRenderer(attRenderer);
			table.getColumnModel().getColumn(1).setMinWidth(100);
			table.getColumnModel().getColumn(2).setCellRenderer(numRenderer);
			table.getColumnModel().getColumn(2).setMinWidth(100);
			table.getColumnModel().getColumn(2).setMaxWidth(100);
			table.getColumnModel().getColumn(3).setCellRenderer(numRenderer);
			table.getColumnModel().getColumn(3).setMinWidth(100);
			table.getColumnModel().getColumn(3).setMaxWidth(100);
			rulesSorter.setTableHeader(table.getTableHeader());			
		}
		return table;
	}
	
	
	/**
	 * This method initializes validationPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */    
	private JPanel getValidationPanel() {
		if (validationPanel == null) {
			java.awt.FlowLayout flowLayout1 = new FlowLayout();
			validationPanel = new JPanel();
			validationPanel.setLayout(flowLayout1);
			flowLayout1.setHgap(10);
			flowLayout1.setVgap(10);
			validationPanel.add(getDatabaseButton(), null);
			validationPanel.add(getXmlButton(), null);
		}
		return validationPanel;
	}
	/**
	 * This method initializes databaseButton	
	 * 	
	 * @return javax.swing.JButton	
	 */    
	private JButton getDatabaseButton() {
		if (databaseButton == null) {
			databaseButton = new JButton();
			databaseButton.setText("Save to Database");
			databaseButton.addActionListener(new java.awt.event.ActionListener() { 
				public void actionPerformed(java.awt.event.ActionEvent e) {
					DatabaseFunctions.saveRulesBasis(new DatabaseManagement(), rulesBasis, relCtxEd);
				}
			});
		}
		return databaseButton;
	}
	/**
	 * This method initializes xmlButton	
	 * 	
	 * @return javax.swing.JButton	
	 */    
	private JButton getXmlButton() {
		if (xmlButton == null) {
			xmlButton = new JButton();
			xmlButton.setText("Export to XML...");
			xmlButton.addActionListener(new java.awt.event.ActionListener() { 
				public void actionPerformed(java.awt.event.ActionEvent e) {
					
					JFileChooser chooser = new JFileChooser();
					chooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
					chooser.setMultiSelectionEnabled(false);
					chooser.setFileFilter(new XML_Filter(""));
					chooser.setDialogTitle("Select the Output File");
					
					if (chooser.showSaveDialog(null) == JFileChooser.APPROVE_OPTION) {
						String fileName = chooser.getSelectedFile().getAbsolutePath();
						if (!fileName.substring(fileName.length()-4, fileName.length()).equals(".xml")) {
							fileName += ".xml";
						}
						boolean isExact = true;
						for (int i=0; isExact==true && i<ruleList.size(); i++) {
							if ( ruleList.get(i).getConfiance() < 1.00 ) {
								isExact = false;
							}
						}
						XmlRuleExport export = new XmlRuleExport();
						if (isExact) {
							export.sauvegardeReglesExactesFichierXML(
									fileName, rulesBasis.getRules(), rulesBasis.getDatasetName(),
									rulesBasis.getMinConfidence(), rulesBasis.getMinSupport());
						} else {
							export.sauvegardeReglesApproximativesFichierXML(
									fileName, rulesBasis.getRules(), rulesBasis.getDatasetName(),
									rulesBasis.getMinConfidence(), rulesBasis.getMinSupport());
						}
					}
				}
			});
		}
		return xmlButton;
	}
	/**
	 * This method initializes connectPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */    
	private JPanel getConnectPanel() {
		if (connectPanel == null) {
			java.awt.FlowLayout flowLayout2 = new FlowLayout();
			connectPanel = new JPanel();
			connectPanel.setLayout(flowLayout2);
			flowLayout2.setHgap(10);
			flowLayout2.setVgap(10);
			connectPanel.add(getConnectButton(), null);
		}
		return connectPanel;
	}
	/**
	 * This method initializes connectButton	
	 * 	
	 * @return javax.swing.JButton	
	 */    
	private JButton getConnectButton() {
		if (connectButton == null) {
			connectButton = new JButton();
			connectButton.setText("Database Connection Parameters...");
			connectButton.addActionListener(new java.awt.event.ActionListener() { 
				public void actionPerformed(java.awt.event.ActionEvent e) {    
					DatabaseConfiguration dc = new DatabaseConfiguration(DatabaseConfiguration.CONFIG_MODE);
				}
			});
		}
		return connectButton;
	}
	/**
	 * This method initializes informationPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */    
	private JPanel getInformationPanel() {
		if (informationPanel == null) {
			relNameLabel = new JLabel();
			nbRelLabel = new JLabel();
			maxConfidenceLabel = new JLabel();
			minConfidenceLabel = new JLabel();
			maxSupportLabel = new JLabel();
			minSupportLabel = new JLabel();
			java.awt.GridBagConstraints gridBagConstraints41 = new GridBagConstraints();
			java.awt.GridBagConstraints gridBagConstraints51 = new GridBagConstraints();
			java.awt.GridBagConstraints gridBagConstraints61 = new GridBagConstraints();
			java.awt.GridBagConstraints gridBagConstraints7 = new GridBagConstraints();
			java.awt.GridBagConstraints gridBagConstraints8 = new GridBagConstraints();
			java.awt.GridBagConstraints gridBagConstraints9 = new GridBagConstraints();
			informationPanel = new JPanel();
			informationPanel.setLayout(new GridBagLayout());
			relNameLabel.setText("Relation Name: " + rulesBasis.getAbstractRelation().getName());
			nbRelLabel.setText("Number of Rules: " + rulesBasis.getNbRules());
			minSupportLabel.setText("Minimal Support: " + rulesBasis.getMinSupport());
			maxSupportLabel.setText("Maximal Support: " + rulesBasis.getMaxSupport());
			minConfidenceLabel.setText("Minimal Confidence: " + rulesBasis.getMinConfidence());
			maxConfidenceLabel.setText("Maximal Confidence: " + rulesBasis.getMaxConfidence());
			maxSupportLabel.setCursor(new java.awt.Cursor(java.awt.Cursor.DEFAULT_CURSOR));
			maxConfidenceLabel.setCursor(new java.awt.Cursor(java.awt.Cursor.DEFAULT_CURSOR));
			gridBagConstraints41.insets = new java.awt.Insets(20,30,5,10);
			gridBagConstraints41.gridx = 1;
			gridBagConstraints41.gridy = 1;
			gridBagConstraints41.weightx = 1.0D;
			gridBagConstraints41.weighty = 1.0D;
			gridBagConstraints41.anchor = java.awt.GridBagConstraints.WEST;
			gridBagConstraints51.insets = new java.awt.Insets(5,30,20,10);
			gridBagConstraints51.gridx = 1;
			gridBagConstraints51.gridy = 2;
			gridBagConstraints51.weightx = 1.0D;
			gridBagConstraints51.weighty = 1.0D;
			gridBagConstraints51.anchor = java.awt.GridBagConstraints.WEST;
			gridBagConstraints61.insets = new java.awt.Insets(20,10,5,10);
			gridBagConstraints61.gridx = 2;
			gridBagConstraints61.gridy = 1;
			gridBagConstraints61.weightx = 1.0D;
			gridBagConstraints61.weighty = 1.0D;
			gridBagConstraints61.anchor = java.awt.GridBagConstraints.WEST;
			gridBagConstraints7.insets = new java.awt.Insets(5,10,20,10);
			gridBagConstraints7.gridx = 2;
			gridBagConstraints7.gridy = 2;
			gridBagConstraints7.weightx = 1.0D;
			gridBagConstraints7.weighty = 1.0D;
			gridBagConstraints7.anchor = java.awt.GridBagConstraints.WEST;
			gridBagConstraints8.insets = new java.awt.Insets(20,10,5,20);
			gridBagConstraints8.gridx = 3;
			gridBagConstraints8.gridy = 1;
			gridBagConstraints8.weightx = 1.0D;
			gridBagConstraints8.weighty = 1.0D;
			gridBagConstraints8.anchor = java.awt.GridBagConstraints.WEST;
			gridBagConstraints9.insets = new java.awt.Insets(5,10,20,20);
			gridBagConstraints9.gridx = 3;
			gridBagConstraints9.gridy = 2;
			gridBagConstraints9.weightx = 1.0D;
			gridBagConstraints9.weighty = 1.0D;
			gridBagConstraints9.anchor = java.awt.GridBagConstraints.WEST;
			informationPanel.add(relNameLabel, gridBagConstraints41);
			informationPanel.add(nbRelLabel, gridBagConstraints51);
			informationPanel.add(minSupportLabel, gridBagConstraints61);
			informationPanel.add(maxSupportLabel, gridBagConstraints7);
			informationPanel.add(minConfidenceLabel, gridBagConstraints8);
			informationPanel.add(maxConfidenceLabel, gridBagConstraints9);
		}
		return informationPanel;
	}
}  //  @jve:decl-index=0:visual-constraint="20,8"
