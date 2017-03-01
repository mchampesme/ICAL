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
 * Created on 2004-06-17
 * @author Manuel Aupetit
 */
package lattice.database.gui;

import javax.swing.JFrame;

import lattice.database.util.DatabaseConnection;
import lattice.database.util.DatabaseFunctions;
import lattice.database.util.DatabaseManagement;
import lattice.gui.RelationalContextEditor;

/**
 * A Swing GUI to configure the database connection parameters 
 * @author Manuel Aupetit
 */
public class DatabaseConfiguration extends JFrame {	/**
     * 
     */
    private static final long serialVersionUID = -4946814491035500605L;

    private javax.swing.JPanel jContentPane = null;
	
	private int mode = 0;
	private DatabaseManagement dbm = null;
	private RelationalContextEditor relCtxEd = null;
	
	private javax.swing.JPanel buttonsPanel = null;
	private javax.swing.JPanel parametersPanel = null;
	private javax.swing.JButton resetButton = null;
	private javax.swing.JButton okButton = null;
	private javax.swing.JButton cancelButton = null;	
	private javax.swing.JLabel serverLabel = null;
	private javax.swing.JTextField serverField = null;
	private javax.swing.JLabel usernameLabel = null;
	private javax.swing.JTextField usernameField = null;
	private javax.swing.JLabel userPasswordLabel = null;
	private javax.swing.JPasswordField userPasswordField = null;
	private javax.swing.JLabel databaseLabel = null;
	private javax.swing.JTextField databaseField = null;
	private javax.swing.JLabel instructionsLabel = null;
	private javax.swing.JPanel resetPanel = null;
	private javax.swing.JPanel validationPanel = null;

	private javax.swing.JCheckBox alwaysUseCheckBox = null;

	// GUI Modes
	public static final int CONFIG_MODE = 1;
	public static final int SAVE_CONTEXTS_MODE = 2;
	public static final int LOAD_CONTEXTS_MODE = 3;
	public static final int DELETE_CONTEXTS_MODE = 4;
	public static final int VIEW_RULES_BASIS_MODE = 5;
	public static final int DELETE_RULES_BASIS_MODE = 6;
	public static final int EXPORT_RULES_BASIS_MODE = 7;
	public static final int SAVE_LATTICE_MODE = 8;
	public static final int VIEW_LATTICE_MODE = 9;
	public static final int DELETE_LATTICES_MODE = 10;
	public static final int EXPORT_LATTICE_MODE = 11;
	public static final int SQL_UPDATE_MODE = 0;

	/****************
	 * Constructors *
	 ****************/
	
	/**
	 * This is the default constructor
	 */
	public DatabaseConfiguration() {
		super();
		this.mode = CONFIG_MODE;
		initialize();
	}

	public DatabaseConfiguration(int mode) {
		super();
		this.mode = mode;
		initialize();
	}
	
	public DatabaseConfiguration(DatabaseManagement dbm, int mode) {
		super();
		this.dbm = dbm;
		this.mode = mode;
		initialize();
	}
	
	public DatabaseConfiguration(DatabaseManagement dbm, RelationalContextEditor relCtxEd, int mode) {
		super();
		this.dbm = dbm;
		this.relCtxEd = relCtxEd;
		this.mode = mode;
		initialize();
	}
	
	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(400, 280);
		this.setContentPane(getJContentPane());
		this.getRootPane().setDefaultButton(getOkButton());
		this.setTitle("MySQL Database Configuration");
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
		this.setResizable(false);
		this.setLocation(60, 40);
		this.setVisible(true);
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
			jContentPane.add(getInstructionsLabel(), java.awt.BorderLayout.NORTH);
			jContentPane.add(getParametersPanel(), java.awt.BorderLayout.CENTER);
			jContentPane.add(getButtonsPanel(), java.awt.BorderLayout.SOUTH);
		}
		return jContentPane;
	}
	/**
	 * This method initializes buttonsPanel
	 * 
	 * @return javax.swing.JPanel
	 */
	private javax.swing.JPanel getButtonsPanel() {
		if(buttonsPanel == null) {
			buttonsPanel = new javax.swing.JPanel();
			java.awt.BorderLayout layBorderLayout11 = new java.awt.BorderLayout();
			layBorderLayout11.setHgap(15);
			layBorderLayout11.setVgap(15);
			buttonsPanel.setLayout(layBorderLayout11);
			buttonsPanel.add(getResetPanel(), java.awt.BorderLayout.WEST);
			buttonsPanel.add(getValidationPanel(), java.awt.BorderLayout.EAST);
		}
		return buttonsPanel;
	}
	/**
	 * This method initializes parametersPanel
	 * 
	 * @return javax.swing.JPanel
	 */
	private javax.swing.JPanel getParametersPanel() {
		if(parametersPanel == null) {
			parametersPanel = new javax.swing.JPanel();
			java.awt.GridBagConstraints consGridBagConstraints3 = new java.awt.GridBagConstraints();
			java.awt.GridBagConstraints consGridBagConstraints5 = new java.awt.GridBagConstraints();
			java.awt.GridBagConstraints consGridBagConstraints4 = new java.awt.GridBagConstraints();
			java.awt.GridBagConstraints consGridBagConstraints7 = new java.awt.GridBagConstraints();
			java.awt.GridBagConstraints consGridBagConstraints8 = new java.awt.GridBagConstraints();
			java.awt.GridBagConstraints consGridBagConstraints9 = new java.awt.GridBagConstraints();
			java.awt.GridBagConstraints consGridBagConstraints10 = new java.awt.GridBagConstraints();
			java.awt.GridBagConstraints consGridBagConstraints6 = new java.awt.GridBagConstraints();
			java.awt.GridBagConstraints consGridBagConstraints1 = new java.awt.GridBagConstraints();
			consGridBagConstraints1.gridx = 2;
			consGridBagConstraints1.gridy = 5;
			consGridBagConstraints1.insets = new java.awt.Insets(5,10,10,20);
			consGridBagConstraints8.gridx = 1;
			consGridBagConstraints8.gridy = 2;
			consGridBagConstraints8.insets = new java.awt.Insets(5,20,5,5);
			consGridBagConstraints7.gridx = 1;
			consGridBagConstraints7.gridy = 1;
			consGridBagConstraints9.gridx = 1;
			consGridBagConstraints9.gridy = 3;
			consGridBagConstraints9.insets = new java.awt.Insets(5,20,5,5);
			consGridBagConstraints10.gridx = 1;
			consGridBagConstraints10.gridy = 4;
			consGridBagConstraints10.insets = new java.awt.Insets(5,20,10,5);
			consGridBagConstraints7.insets = new java.awt.Insets(10,20,5,5);
			consGridBagConstraints3.weightx = 1.0;
			consGridBagConstraints3.fill = java.awt.GridBagConstraints.HORIZONTAL;
			consGridBagConstraints3.gridx = 2;
			consGridBagConstraints3.gridy = 1;
			consGridBagConstraints5.weightx = 1.0;
			consGridBagConstraints5.fill = java.awt.GridBagConstraints.HORIZONTAL;
			consGridBagConstraints4.weightx = 1.0;
			consGridBagConstraints4.fill = java.awt.GridBagConstraints.HORIZONTAL;
			consGridBagConstraints4.gridx = 2;
			consGridBagConstraints4.gridy = 2;
			consGridBagConstraints5.gridx = 2;
			consGridBagConstraints5.gridy = 3;
			consGridBagConstraints5.insets = new java.awt.Insets(5,5,5,20);
			consGridBagConstraints6.weightx = 1.0;
			consGridBagConstraints6.fill = java.awt.GridBagConstraints.HORIZONTAL;
			consGridBagConstraints6.gridx = 2;
			consGridBagConstraints6.gridy = 4;
			consGridBagConstraints6.insets = new java.awt.Insets(5,5,5,20);
			consGridBagConstraints7.anchor = java.awt.GridBagConstraints.EAST;
			consGridBagConstraints9.anchor = java.awt.GridBagConstraints.EAST;
			consGridBagConstraints4.insets = new java.awt.Insets(5,5,5,20);
			consGridBagConstraints3.insets = new java.awt.Insets(10,5,5,20);
			consGridBagConstraints10.anchor = java.awt.GridBagConstraints.EAST;
			consGridBagConstraints8.anchor = java.awt.GridBagConstraints.EAST;
			parametersPanel.setLayout(new java.awt.GridBagLayout());
			parametersPanel.add(getServerLabel(), consGridBagConstraints7);
			parametersPanel.add(getServerField(), consGridBagConstraints3);
			parametersPanel.add(getUsernameLabel(), consGridBagConstraints8);
			parametersPanel.add(getUsernameField(), consGridBagConstraints4);
			parametersPanel.add(getUserPasswordLabel(), consGridBagConstraints9);
			parametersPanel.add(getUserPasswordField(), consGridBagConstraints5);
			parametersPanel.add(getDatabaseLabel(), consGridBagConstraints10);
			parametersPanel.add(getDatabaseField(), consGridBagConstraints6);
			parametersPanel.add(getAlwaysUseCheckBox(), consGridBagConstraints1);
			parametersPanel.setMinimumSize(new java.awt.Dimension(335,337));
		}
		return parametersPanel;
	}
	/**
	 * This method initializes resetButton
	 * 
	 * @return javax.swing.JButton
	 */
	private javax.swing.JButton getResetButton() {
		if(resetButton == null) {
			resetButton = new javax.swing.JButton();
			resetButton.setText("Reset to Default");
			resetButton.addActionListener(new java.awt.event.ActionListener() { 
				public void actionPerformed(java.awt.event.ActionEvent e) {    
					DatabaseConnection.setDefaultParameters();
					refreshFields();
				}
			});
		}
		return resetButton;
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
					
					DatabaseConnection.setParameters(
								serverField.getText(),
								usernameField.getText(),
								new String(userPasswordField.getPassword()),
								databaseField.getText(),
								alwaysUseCheckBox.isSelected());
					
					if (mode != CONFIG_MODE) {
						
						dbm = new DatabaseManagement();
						
						if (mode == SAVE_CONTEXTS_MODE) {
							new SaveContextsDialog(dbm, relCtxEd);
						}
						else if (mode == LOAD_CONTEXTS_MODE) {
							new LoadContextsDialog(dbm, relCtxEd);
						}
						else if (mode == DELETE_CONTEXTS_MODE) {
							new DeleteContextsDialog(dbm);
						}
						else if (mode == VIEW_RULES_BASIS_MODE) {
							DatabaseFunctions.viewRulesBasis(dbm, relCtxEd);
						}
						else if (mode == DELETE_RULES_BASIS_MODE) {
							new DeleteRulesBasisDialog(dbm);
						}
						else if (mode == EXPORT_RULES_BASIS_MODE) {
							DatabaseFunctions.exportRulesBasisToXML(dbm, relCtxEd);
						}
						else if (mode == SAVE_LATTICE_MODE) {
							DatabaseFunctions.saveLattice(dbm, relCtxEd);
						}
						else if (mode == VIEW_LATTICE_MODE) {
							DatabaseFunctions.viewLattice(dbm, relCtxEd);
						}
						else if (mode == DELETE_LATTICES_MODE) {
							new DeleteLatticesDialog(dbm);
						}
						else if (mode == EXPORT_LATTICE_MODE) {
							DatabaseFunctions.exportLatticeToXML(dbm, relCtxEd);
						}
						else if (mode == SQL_UPDATE_MODE) {
							DatabaseFunctions.sqlUpdate(
								dbm,
								DatabaseFunctions.showInputDialog("Enter your SQL Update Query:"));
						}
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
					dispose();
				}
			});
		}
		return cancelButton;
	}
	/**
	 * This method initializes serverLabel
	 * 
	 * @return javax.swing.JLabel
	 */
	private javax.swing.JLabel getServerLabel() {
		if(serverLabel == null) {
			serverLabel = new javax.swing.JLabel();
			serverLabel.setText("MySQL Server:");
		}
		return serverLabel;
	}
	/**
	 * This method initializes serverField
	 * 
	 * @return javax.swing.JTextField
	 */
	private javax.swing.JTextField getServerField() {
		if(serverField == null) {
			serverField = new javax.swing.JTextField();
			serverField.setText(DatabaseConnection.getServer());
		}
		return serverField;
	}
	/**
	 * This method initializes usernameLabel
	 * 
	 * @return javax.swing.JLabel
	 */
	private javax.swing.JLabel getUsernameLabel() {
		if(usernameLabel == null) {
			usernameLabel = new javax.swing.JLabel();
			usernameLabel.setText("Username:");
		}
		return usernameLabel;
	}
	/**
	 * This method initializes usernameField
	 * 
	 * @return javax.swing.JTextField
	 */
	private javax.swing.JTextField getUsernameField() {
		if(usernameField == null) {
			usernameField = new javax.swing.JTextField();
			usernameField.setText(DatabaseConnection.getUsername());
		}
		return usernameField;
	}
	/**
	 * This method initializes userPasswordLabel
	 * 
	 * @return javax.swing.JLabel
	 */
	private javax.swing.JLabel getUserPasswordLabel() {
		if(userPasswordLabel == null) {
			userPasswordLabel = new javax.swing.JLabel();
			userPasswordLabel.setText("Password:");
		}
		return userPasswordLabel;
	}
	/**
	 * This method initializes userPasswordField
	 * 
	 * @return javax.swing.JPasswordField
	 */
	private javax.swing.JPasswordField getUserPasswordField() {
		if(userPasswordField == null) {
			userPasswordField = new javax.swing.JPasswordField();
			userPasswordField.setText(DatabaseConnection.getPassword());
		}
		return userPasswordField;
	}
	/**
	 * This method initializes databaseLabel
	 * 
	 * @return javax.swing.JLabel
	 */
	private javax.swing.JLabel getDatabaseLabel() {
		if(databaseLabel == null) {
			databaseLabel = new javax.swing.JLabel();
			databaseLabel.setText("Existing Database Name:");
		}
		return databaseLabel;
	}
	/**
	 * This method initializes databaseField
	 * 
	 * @return javax.swing.JTextField
	 */
	private javax.swing.JTextField getDatabaseField() {
		if(databaseField == null) {
			databaseField = new javax.swing.JTextField();
			databaseField.setText(DatabaseConnection.getDatabase());
		}
		return databaseField;
	}
	
	private void refreshFields() {
		serverField.setText(DatabaseConnection.getServer());
		usernameField.setText(DatabaseConnection.getUsername());
		userPasswordField.setText(DatabaseConnection.getPassword());
		databaseField.setText(DatabaseConnection.getDatabase());
	}
	
	/**
	 * This method initializes instructionsLabel
	 * 
	 * @return javax.swing.JLabel
	 */
	private javax.swing.JLabel getInstructionsLabel() {
		if(instructionsLabel == null) {
			instructionsLabel = new javax.swing.JLabel();
			instructionsLabel.setText("Enter the connection parameters for your MySQL database");
			instructionsLabel.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
			instructionsLabel.setPreferredSize(new java.awt.Dimension(284,34));
			instructionsLabel.setHorizontalTextPosition(javax.swing.SwingConstants.CENTER);
			instructionsLabel.setVerticalAlignment(javax.swing.SwingConstants.BOTTOM);
		}
		return instructionsLabel;
	}
	/**
	 * This method initializes resetPanel
	 * 
	 * @return javax.swing.JPanel
	 */
	private javax.swing.JPanel getResetPanel() {
		if(resetPanel == null) {
			resetPanel = new javax.swing.JPanel();
			java.awt.FlowLayout layFlowLayout13 = new java.awt.FlowLayout();
			layFlowLayout13.setHgap(10);
			layFlowLayout13.setVgap(10);
			resetPanel.setLayout(layFlowLayout13);
			resetPanel.add(getResetButton(), null);
		}
		return resetPanel;
	}
	/**
	 * This method initializes validationPanel
	 * 
	 * @return javax.swing.JPanel
	 */
	private javax.swing.JPanel getValidationPanel() {
		if(validationPanel == null) {
			validationPanel = new javax.swing.JPanel();
			java.awt.FlowLayout layFlowLayout12 = new java.awt.FlowLayout();
			layFlowLayout12.setHgap(10);
			layFlowLayout12.setVgap(10);
			validationPanel.setLayout(layFlowLayout12);
			validationPanel.add(getOkButton(), null);
			validationPanel.add(getCancelButton(), null);
		}
		return validationPanel;
	}
	/**
	 * This method initializes alwaysUseCheckBox
	 * 
	 * @return javax.swing.JCheckBox
	 */
	private javax.swing.JCheckBox getAlwaysUseCheckBox() {
		if(alwaysUseCheckBox == null) {
			alwaysUseCheckBox = new javax.swing.JCheckBox();
			alwaysUseCheckBox.setText("Always use these parameters");
			alwaysUseCheckBox.setToolTipText("This window will not appear for each action if checked");
			alwaysUseCheckBox.setSelected(DatabaseConnection.getAlwaysUseParameters());
		}
		return alwaysUseCheckBox;
	}
}  //  @jve:visual-info  decl-index=0 visual-constraint="10,10"
