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
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Point;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.table.AbstractTableModel;

import lattice.database.util.DatabaseFunctions;
import lattice.gui.RelationalContextEditor;
import rule.util.IntentInstance;
import rule.util.IntentsBasis;
import javax.swing.JLabel;
import java.awt.FlowLayout;

/**
 * A Swing GUI to visualize Intents, should be modified because it has no real use yet
 * @author Manuel Aupetit
 */
public class IntentsTableVisualization extends JFrame {
	
	private IntentsBasis intentsBasis = null;
	private RelationalContextEditor relCtxEd = null;
	public static Point location = new Point(60, 40);
	
	private javax.swing.JPanel jContentPane = null;
	
	private JPanel mainPanel = null;
	private JPanel filterButtonsPanel = null;
	private JButton premiseFilterButton = null;
	private JButton confidenceFilterButton = null;
	private JTable table = null;
	private JScrollPane intentsScrollPane = null;
	
	private JPanel bottomPanel = null;
	private JLabel latticeDescriptionLabel = null;
	private JLabel nbIntentsLabel = null;
	private JButton exitButton = null;
	private JPanel exitPanel = null;
	private JLabel minSupportLabel = null;
	private JPanel informationPanel = null;
	private JLabel maxSupportLabel = null;
	/**
	 * 
	 * @param intentsBasis
	 * @param relCtxEd
	 */
	public IntentsTableVisualization(IntentsBasis intentsBasis, RelationalContextEditor relCtxEd) {
		super();
		this.relCtxEd = relCtxEd;
		if (intentsBasis.getIntents() != null && !intentsBasis.getIntents().isEmpty()) {
			this.intentsBasis = intentsBasis;
			initialize();
		} else {
			DatabaseFunctions.showMessageDialog("No intents generated");
		}
	}
	
	/**
	 * This method initializes this	
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setTitle("Intents Table Visualization");
		this.setSize(550, 400);
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
		}
		return jContentPane;
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
			mainPanel.add(getIntentsScrollPane(), java.awt.BorderLayout.CENTER);
			mainPanel.add(getBottomPanel(), java.awt.BorderLayout.SOUTH);
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
			java.awt.GridBagConstraints gridBagConstraints3 = new GridBagConstraints();
			filterButtonsPanel = new JPanel();
			filterButtonsPanel.setLayout(new GridBagLayout());
			gridBagConstraints3.gridx = 1;
			gridBagConstraints3.weightx = 1.0D;
			gridBagConstraints3.insets = new java.awt.Insets(20,15,10,15);
			gridBagConstraints6.gridx = 4;
			gridBagConstraints6.weightx = 0.0D;
			gridBagConstraints6.insets = new java.awt.Insets(20,15,10,30);
			filterButtonsPanel.add(getPremiseFilterButton(), gridBagConstraints3);
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
					new AttributesFilter(intentsBasis, AttributesFilter.INTENT_MODE, relCtxEd);
				} 
			});
		}
		return premiseFilterButton;
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
					new ExtremumFilter(intentsBasis, ExtremumFilter.INTENTS_BASIS_SUPPORT_MODE, relCtxEd);
				}   
			});
		}
		return confidenceFilterButton;
	}
	/**
	 * This method initializes intentsScrollPane	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */    
	private JScrollPane getIntentsScrollPane() {
		if (intentsScrollPane == null) {
			intentsScrollPane = new JScrollPane();
			intentsScrollPane.setViewportView(getIntentsBasisTable());
			intentsScrollPane.setHorizontalScrollBarPolicy(javax.swing.JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);
			intentsScrollPane.setVerticalScrollBarPolicy(javax.swing.JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
		}
		return intentsScrollPane;
	}
	
	
	/**
	 * 
	 * @author Manuel Aupetit
	 *
	 */
	class IntentsTableModel extends AbstractTableModel {
		
		public final String[] columnNames = {"Intent", "Support"};
		private Object[][] intentsValues;
		
		public IntentsTableModel() {
			setIntentsValues();
		}
		
		public void setIntentsValues() {
			int nbIntents = intentsBasis.getIntents().size();
			this.intentsValues = new Object[nbIntents][2];
			for (int row=0; row<nbIntents; row++) {
				IntentInstance currentIntent = (IntentInstance)intentsBasis.getIntents().get(row);
				intentsValues[row][0] = currentIntent.getIntent().toString();
				intentsValues[row][1] = new Double(currentIntent.getSupport());
			}
		}
		
		public int getRowCount() {
			return intentsValues.length;
		}
		
		public int getColumnCount() {
			return intentsValues[0].length;
		} 
		
		public Object getValueAt(int row, int column) {
			return intentsValues[row][column];
		} 
		
		public String getColumnName(int column) {
			return columnNames[column];
		}
	}
	
	
	/**
	 * This method initializes intentsBasisTable	
	 * 	
	 * @return javax.swing.JTable	
	 */    
	private JTable getIntentsBasisTable() {
		if (table == null) {
			TableSorter intentsSorter = new TableSorter(new IntentsTableModel());
			table = new JTable(intentsSorter);
			
			table.getTableHeader().setReorderingAllowed(false);
			table.getTableHeader().setResizingAllowed(false);
			
			AttributesColumnRenderer attRenderer = new AttributesColumnRenderer();
			NumericColumnRenderer numRenderer = new NumericColumnRenderer();
			table.getColumnModel().getColumn(0).setCellRenderer(attRenderer);
			table.getColumnModel().getColumn(0).setMinWidth(100);
			table.getColumnModel().getColumn(1).setCellRenderer(numRenderer);
			table.getColumnModel().getColumn(1).setMinWidth(100);
			table.getColumnModel().getColumn(1).setMaxWidth(100);
			intentsSorter.setTableHeader(table.getTableHeader());			
		}
		return table;
	}
	
	
	/**
	 * This method initializes bottomPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */    
	private JPanel getBottomPanel() {
		if (bottomPanel == null) {
			java.awt.BorderLayout borderLayout1 = new BorderLayout();
			latticeDescriptionLabel = new JLabel();
			bottomPanel = new JPanel();
			bottomPanel.setLayout(borderLayout1);
			latticeDescriptionLabel.setText(intentsBasis.getLatticeDescription());
			bottomPanel.add(latticeDescriptionLabel, java.awt.BorderLayout.NORTH);
			latticeDescriptionLabel.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
			latticeDescriptionLabel.setHorizontalTextPosition(javax.swing.SwingConstants.CENTER);
			latticeDescriptionLabel.setVerticalTextPosition(javax.swing.SwingConstants.BOTTOM);
			latticeDescriptionLabel.setVerticalAlignment(javax.swing.SwingConstants.BOTTOM);
			latticeDescriptionLabel.setMaximumSize(new java.awt.Dimension(31,35));
			latticeDescriptionLabel.setMinimumSize(new java.awt.Dimension(31,35));
			latticeDescriptionLabel.setPreferredSize(new java.awt.Dimension(31,35));
			bottomPanel.add(getInformationPanel(), java.awt.BorderLayout.CENTER);
			bottomPanel.add(getExitPanel(), java.awt.BorderLayout.EAST);
		}
		return bottomPanel;
	}
	/**
	 * This method initializes exitButton	
	 * 	
	 * @return javax.swing.JButton	
	 */    
	private JButton getExitButton() {
		if (exitButton == null) {
			exitButton = new JButton();
			exitButton.setText("Exit");
			exitButton.addActionListener(new java.awt.event.ActionListener() { 
				public void actionPerformed(java.awt.event.ActionEvent e) {    
					dispose();
				}
			});
		}
		return exitButton;
	}
	/**
	 * This method initializes exitPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */    
	private JPanel getExitPanel() {
		if (exitPanel == null) {
			java.awt.FlowLayout flowLayout2 = new FlowLayout();
			exitPanel = new JPanel();
			exitPanel.setLayout(flowLayout2);
			flowLayout2.setHgap(10);
			flowLayout2.setVgap(10);
			exitPanel.add(getExitButton(), null);
		}
		return exitPanel;
	}
	/**
	 * This method initializes informationPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */    
	private JPanel getInformationPanel() {
		if (informationPanel == null) {
			java.awt.GridBagConstraints gridBagConstraints31 = new GridBagConstraints();
			java.awt.GridBagConstraints gridBagConstraints2 = new GridBagConstraints();
			java.awt.GridBagConstraints gridBagConstraints1 = new GridBagConstraints();
			minSupportLabel = new JLabel();
			maxSupportLabel = new JLabel();
			nbIntentsLabel = new JLabel();
			informationPanel = new JPanel();
			informationPanel.setLayout(new GridBagLayout());
			minSupportLabel.setText("Minimal Support: " + intentsBasis.getMinSupport());
			maxSupportLabel.setText("Maximal Support: " + intentsBasis.getMaxSupport());
			nbIntentsLabel.setText("Number of Intents: " + intentsBasis.getIntents().size());
			gridBagConstraints1.gridx = 1;
			gridBagConstraints1.insets = new java.awt.Insets(10,10,10,10);
			gridBagConstraints1.weightx = 1.0D;
			gridBagConstraints2.gridx = 2;
			gridBagConstraints2.insets = new java.awt.Insets(10,10,10,10);
			gridBagConstraints2.weightx = 1.0D;
			gridBagConstraints31.gridx = 3;
			gridBagConstraints31.insets = new java.awt.Insets(10,10,10,10);
			gridBagConstraints31.weightx = 1.0D;
			informationPanel.add(minSupportLabel, gridBagConstraints1);
			informationPanel.add(maxSupportLabel, gridBagConstraints2);
			informationPanel.add(nbIntentsLabel, gridBagConstraints31);
		}
		return informationPanel;
	}
}  //  @jve:decl-index=0:visual-constraint="20,8"
