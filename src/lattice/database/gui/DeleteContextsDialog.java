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
 * Created on 13 juil. 2004
 * @author Manuel Aupetit
 */
package lattice.database.gui;

import java.util.Vector;

import javax.swing.JCheckBox;
import javax.swing.JFrame;

import lattice.database.util.DatabaseConnection;
import lattice.database.util.DatabaseFunctions;
import lattice.database.util.DatabaseManagement;

/**
 * A Swing GUI to configure the contexts to delete from the database
 * @author Manuel Aupetit
 */
public class DeleteContextsDialog extends JFrame {	/**
     * 
     */
    private static final long serialVersionUID = -7667621891435802476L;

    private javax.swing.JPanel jContentPane = null;

	private DatabaseManagement dbm = null;

	private javax.swing.JCheckBox[] checkBoxes = null;

	private javax.swing.JPanel instructionsPanel = null;
	private javax.swing.JPanel buttonsPanel = null;
	private javax.swing.JScrollPane tableScrollPane = null;
	private javax.swing.JPanel connectPanel = null;
	private javax.swing.JPanel validationPanel = null;
	private javax.swing.JButton connectButton = null;
	private javax.swing.JButton okButton = null;
	private javax.swing.JButton cancelButton = null;
	private javax.swing.JLabel instructionsLabel = null;
	private javax.swing.JPanel dbNamePanel = null;
	private javax.swing.JLabel dbNameLabel = null;
	private javax.swing.JPanel tableChoicePanel = null;
	
	
	/**
	 * Constructor using a database management parameter 
	 */
	public DeleteContextsDialog(DatabaseManagement dbm) {
		super();
		this.dbm = dbm;
		initialize();
	}


	/**
	 * This method initializes this
	 * 
	 */
	private void initialize() {
		this.setSize(400, 280);
		this.setContentPane(getJContentPane());
		this.getRootPane().setDefaultButton(getOkButton());
		this.setLocation(60, 40);
		this.setTitle("Delete Contexts");
		this.setVisible(true);
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
	}
	
	
	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private javax.swing.JPanel getJContentPane() {
		if (jContentPane == null) {
			jContentPane = new javax.swing.JPanel();
			jContentPane.setLayout(new java.awt.BorderLayout());
			jContentPane.add(getInstructionsPanel(), java.awt.BorderLayout.NORTH);
			jContentPane.add(getTableScrollPane(), java.awt.BorderLayout.CENTER);
			jContentPane.add(getButtonsPanel(), java.awt.BorderLayout.SOUTH);
		}
		return jContentPane;
	}
	/**
	 * This method initializes instructionsPanel
	 * 
	 * @return javax.swing.JPanel
	 */
	private javax.swing.JPanel getInstructionsPanel() {
		if(instructionsPanel == null) {
			instructionsPanel = new javax.swing.JPanel();
			instructionsPanel.setLayout(new java.awt.BorderLayout());
			instructionsPanel.add(getInstructionsLabel(), java.awt.BorderLayout.CENTER);
			instructionsPanel.add(getDbNamePanel(), java.awt.BorderLayout.SOUTH);
			instructionsPanel.setMinimumSize(new java.awt.Dimension(311,64));
			instructionsPanel.setPreferredSize(new java.awt.Dimension(311,64));
		}
		return instructionsPanel;
	}
	/**
	 * This method initializes buttonsPanel
	 * 
	 * @return javax.swing.JPanel
	 */
	private javax.swing.JPanel getButtonsPanel() {
		if(buttonsPanel == null) {
			buttonsPanel = new javax.swing.JPanel();
			buttonsPanel.setLayout(new java.awt.BorderLayout());
			buttonsPanel.add(getConnectPanel(), java.awt.BorderLayout.WEST);
			buttonsPanel.add(getValidationPanel(), java.awt.BorderLayout.EAST);
		}
		return buttonsPanel;
	}
	/**
	 * This method initializes tableScrollPane
	 * 
	 * @return javax.swing.JScrollPane
	 */
	private javax.swing.JScrollPane getTableScrollPane() {
		if(tableScrollPane == null) {
			tableScrollPane = new javax.swing.JScrollPane();
			tableScrollPane.setViewportView(getTableChoicePanel());
		}
		return tableScrollPane;
	}
	/**
	 * This method initializes connectPanel
	 * 
	 * @return javax.swing.JPanel
	 */
	private javax.swing.JPanel getConnectPanel() {
		if(connectPanel == null) {
			connectPanel = new javax.swing.JPanel();
			java.awt.FlowLayout layFlowLayout1 = new java.awt.FlowLayout();
			layFlowLayout1.setHgap(10);
			layFlowLayout1.setVgap(10);
			connectPanel.setLayout(layFlowLayout1);
			connectPanel.add(getConnectButton(), null);
		}
		return connectPanel;
	}
	/**
	 * This method initializes validationPanel
	 * 
	 * @return javax.swing.JPanel
	 */
	private javax.swing.JPanel getValidationPanel() {
		if(validationPanel == null) {
			validationPanel = new javax.swing.JPanel();
			java.awt.FlowLayout layFlowLayout2 = new java.awt.FlowLayout();
			layFlowLayout2.setHgap(10);
			layFlowLayout2.setVgap(10);
			validationPanel.setLayout(layFlowLayout2);
			validationPanel.add(getOkButton(), null);
			validationPanel.add(getCancelButton(), null);
		}
		return validationPanel;
	}
	/**
	 * This method initializes connectButton
	 * 
	 * @return javax.swing.JButton
	 */
	private javax.swing.JButton getConnectButton() {
		if(connectButton == null) {
			connectButton = new javax.swing.JButton();
			connectButton.setText("Connection Parameters...");
			connectButton.addActionListener(new java.awt.event.ActionListener() { 
				public void actionPerformed(java.awt.event.ActionEvent e) {    
					DatabaseConfiguration dbc = new DatabaseConfiguration(dbm, DatabaseConfiguration.DELETE_CONTEXTS_MODE);
					dispose();
				}
			});
		}
		return connectButton;
	}
	/**
	 * This method initializes okButton
	 * 
	 * @return javax.swing.JButton
	 */
	private javax.swing.JButton getOkButton() {
		if(okButton == null) {
			okButton = new javax.swing.JButton();
			okButton.setText("OK");
			okButton.addActionListener(new java.awt.event.ActionListener() { 
				public void actionPerformed(java.awt.event.ActionEvent e) {

					if (DatabaseFunctions.showWarningDialog(
						"All the Inter-Object relations derived from contexts you selected will also be deleted")) {

						Vector relations = new Vector();
						for (int i=0; i<getCheckBoxes().length; i++) {
							if (getCheckBoxes()[i].isSelected()) {
								relations.addElement(dbm.getTables().get(i));
							}
						}
						DatabaseFunctions.deleteContexts(dbm, relations);
					}
					dispose();
				}
			});
		}
		return okButton;
	}
	/**
	 * This method initializes cancelButton
	 * 
	 * @return javax.swing.JButton
	 */
	private javax.swing.JButton getCancelButton() {
		if(cancelButton == null) {
			cancelButton = new javax.swing.JButton();
			cancelButton.setText("Cancel");
			cancelButton.addActionListener(new java.awt.event.ActionListener() { 
				public void actionPerformed(java.awt.event.ActionEvent e) {
					dbm.closeConnection();    
					dispose();
				}
			});
		}
		return cancelButton;
	}
	/**
	 * This method initializes instructionsLabel
	 * 
	 * @return javax.swing.JLabel
	 */
	private javax.swing.JLabel getInstructionsLabel() {
		if(instructionsLabel == null) {
			instructionsLabel = new javax.swing.JLabel();
			instructionsLabel.setText("Select the tables you want to delete from the selected database:");
			instructionsLabel.setVerticalAlignment(javax.swing.SwingConstants.BOTTOM);
			instructionsLabel.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
		}
		return instructionsLabel;
	}
	/**
	 * This method initializes dbNamePanel
	 * 
	 * @return javax.swing.JPanel
	 */
	private javax.swing.JPanel getDbNamePanel() {
		if(dbNamePanel == null) {
			dbNamePanel = new javax.swing.JPanel();
			java.awt.GridBagConstraints consGridBagConstraints6 = new java.awt.GridBagConstraints();
			consGridBagConstraints6.insets = new java.awt.Insets(10,20,10,5);
			dbNamePanel.setLayout(new java.awt.GridBagLayout());
			dbNamePanel.add(getDbNameLabel(), consGridBagConstraints6);
		}
		return dbNamePanel;
	}
	/**
	 * This method initializes dbNameLabel
	 * 
	 * @return javax.swing.JLabel
	 */
	private javax.swing.JLabel getDbNameLabel() {
		if(dbNameLabel == null) {
			dbNameLabel = new javax.swing.JLabel();
			dbNameLabel.setText("'" + DatabaseConnection.getDatabase() + "'");
		}
		return dbNameLabel;
	}

	private javax.swing.JPanel getTableChoicePanel() {
		if(tableChoicePanel == null) {
			tableChoicePanel = new javax.swing.JPanel();
			java.awt.GridBagConstraints consGridBagConstraints9 = new java.awt.GridBagConstraints();
			consGridBagConstraints9.gridx = 0;
			consGridBagConstraints9.anchor = java.awt.GridBagConstraints.WEST;
			tableChoicePanel.setLayout(new java.awt.GridBagLayout());
			for (int i=0; i<getCheckBoxes().length; i++) {
				consGridBagConstraints9.gridy = i;
				tableChoicePanel.add(getCheckBoxes()[i], consGridBagConstraints9);
			}
		}
		return tableChoicePanel;
	}

	private javax.swing.JCheckBox[] getCheckBoxes() {
		if (checkBoxes == null) {
			refreshTables();
		}
		return checkBoxes;
	}
	
	private void refreshTables() {
		Vector tables = dbm.getTables();
		this.checkBoxes = new JCheckBox[tables.size()];
		for (int i=0; i<tables.size(); i++) {
			checkBoxes[i] = new JCheckBox(
				tables.get(i) + " [" +
				dbm.getRelationType((String)tables.get(i)) +
				" Relation]", true);
		}
	}

}
