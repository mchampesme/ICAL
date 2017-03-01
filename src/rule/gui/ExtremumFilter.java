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
 * Created on 2004-08-26
 * @author Manuel Aupetit
 */
package rule.gui;

import java.awt.FlowLayout;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTextField;

import lattice.database.util.DatabaseFunctions;
import lattice.gui.RelationalContextEditor;
import rule.util.IntentsBasis;
import rule.util.RulesBasis;
/**
 * A Swing GUI to filter support and confidence values for the rules basis visualization 
 * @author Manuel Aupetit
 */
public class ExtremumFilter extends JFrame {

	private javax.swing.JPanel jContentPane = null;
	private RulesBasis rulesBasis = null;
	private IntentsBasis intentsBasis = null;
	private RelationalContextEditor relCtxEd = null;
	private int mode = 0;
	
	public static final int RULES_BASIS_SUPPORT_MODE = 1;
	public static final int RULES_BASIS_CONFIDENCE_MODE = 2;
	public static final int INTENTS_BASIS_SUPPORT_MODE = 3;

	private JPanel jPanel = null;
	private JPanel validationPanel = null;
	private JButton okButton = null;
	private JButton cancelButton = null;
	private JLabel instructionLabel = null;
	private JLabel minLabel = null;
	private JTextField minTextField = null;
	private JLabel infLabel = null;
	private JTextField maxTextField = null;
	private JLabel maxLabel = null;

	/**
	 * 
	 * @param rulesBasis
	 * @param mode
	 * @param relCtxEd
	 */
	public ExtremumFilter(RulesBasis rulesBasis, int mode, RelationalContextEditor relCtxEd) {
		super();
		this.rulesBasis = rulesBasis;
		this.relCtxEd = relCtxEd;
		this.mode = mode;
		initialize();
	}
	
	/**
	 * 
	 * @param intentsBasis
	 * @param mode
	 * @param relCtxEd
	 */
	public ExtremumFilter(IntentsBasis intentsBasis, int mode, RelationalContextEditor relCtxEd) {
		super();
		this.intentsBasis = intentsBasis;
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
		this.setResizable(false);
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
		this.setTitle("Extremum Values");
		this.setSize(300,180);
		this.setLocation(300, 100);
		this.setContentPane(getJContentPane());
		this.getRootPane().setDefaultButton(getOkButton());
		this.setVisible(true);
	}
	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private javax.swing.JPanel getJContentPane() {
		if(jContentPane == null) {
			instructionLabel = new JLabel();
			jContentPane = new javax.swing.JPanel();
			jContentPane.setLayout(new java.awt.BorderLayout());
			instructionLabel.setText("Select the new minimal and maximal values:");
			instructionLabel.setPreferredSize(new java.awt.Dimension(216,55));
			instructionLabel.setVerticalAlignment(javax.swing.SwingConstants.CENTER);
			instructionLabel.setVerticalTextPosition(javax.swing.SwingConstants.BOTTOM);
			instructionLabel.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
			jContentPane.add(instructionLabel, java.awt.BorderLayout.NORTH);
			jContentPane.add(getJPanel(), java.awt.BorderLayout.CENTER);
			jContentPane.add(getValidationPanel(), java.awt.BorderLayout.SOUTH);
		}
		return jContentPane;
	}
	/**
	 * This method initializes jPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */    
	private JPanel getJPanel() {
		if (jPanel == null) {
			maxLabel = new JLabel();
			infLabel = new JLabel();
			minLabel = new JLabel();
			jPanel = new JPanel();
			String min = "0.0 <=";
			String max = "<= 1.0";
			if (mode == RULES_BASIS_SUPPORT_MODE) {
				min = rulesBasis.getMinSupport() + " <=";
				max = "<= " + rulesBasis.getMaxSupport();
			} else if (mode == RULES_BASIS_CONFIDENCE_MODE) {
				min = rulesBasis.getMinConfidence() + " <=";
				max = "<= " + rulesBasis.getMaxConfidence();
			} else if (mode == INTENTS_BASIS_SUPPORT_MODE) {
				min = intentsBasis.getMinSupport() + " <=";
				max = "<= " + intentsBasis.getMaxSupport();
			}
			minLabel.setText(min);
			infLabel.setText("<=");
			maxLabel.setText(max);
			jPanel.add(minLabel, null);
			jPanel.add(getMinTextField(), null);
			jPanel.add(infLabel, null);
			jPanel.add(getMaxTextField(), null);
			jPanel.add(maxLabel, null);
		}
		return jPanel;
	}
	/**
	 * This method initializes validationPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */    
	private JPanel getValidationPanel() {
		if (validationPanel == null) {
			java.awt.FlowLayout flowLayout3 = new FlowLayout();
			validationPanel = new JPanel();
			validationPanel.setLayout(flowLayout3);
			flowLayout3.setHgap(10);
			flowLayout3.setVgap(10);
			validationPanel.add(getOkButton(), null);
			validationPanel.add(getCancelButton(), null);
		}
		return validationPanel;
	}
	/**
	 * This method initializes okButton	
	 * 	
	 * @return javax.swing.JButton	
	 */    
	private JButton getOkButton() {
		if (okButton == null) {
			okButton = new JButton();
			okButton.setText("OK");
			okButton.addActionListener(new java.awt.event.ActionListener() { 
				public void actionPerformed(java.awt.event.ActionEvent e) {
					try {
						double minValue = Double.parseDouble(minTextField.getText());
						double maxValue = Double.parseDouble(maxTextField.getText());
						if (minValue <= maxValue) {
							if (mode == RULES_BASIS_SUPPORT_MODE) {
								if (minValue >= rulesBasis.getMinSupport() && maxValue <= rulesBasis.getMaxSupport()) {
									new TableVisualization(
											rulesBasis.filterRulesBySupport(minValue, maxValue), relCtxEd);
									dispose();
								} else {
									DatabaseFunctions.showMessageDialog("Incorrect values");
								}
							}
							else if (mode == RULES_BASIS_CONFIDENCE_MODE) {
								if (minValue >= rulesBasis.getMinConfidence() && maxValue <= rulesBasis.getMaxConfidence()) {
									new TableVisualization(
											rulesBasis.filterRulesByConfidence(minValue, maxValue), relCtxEd);
									dispose();
								} else {
									DatabaseFunctions.showMessageDialog("Incorrect values");
								}
							}
							else if (mode == INTENTS_BASIS_SUPPORT_MODE) {
								if (minValue >= intentsBasis.getMinSupport() && maxValue <= intentsBasis.getMaxSupport()) {
									new IntentsTableVisualization(
											intentsBasis.filterIntentsBySupport(minValue, maxValue), relCtxEd);
									dispose();
								} else {
									DatabaseFunctions.showMessageDialog("Incorrect values");
								}
							}
						} else {
							DatabaseFunctions.showMessageDialog("Incorrect values");
						}
					} catch (NumberFormatException ex) {
						DatabaseFunctions.showMessageDialog("Incorrect values");
					}
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
	private JButton getCancelButton() {
		if (cancelButton == null) {
			cancelButton = new JButton();
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
	 * This method initializes minTextField	
	 * 	
	 * @return javax.swing.JTextField	
	 */    
	private JTextField getMinTextField() {
		if (minTextField == null) {
			minTextField = new JTextField();
			if (mode == RULES_BASIS_SUPPORT_MODE) {
				minTextField.setText(""+rulesBasis.getMinSupport());
			} else if (mode == RULES_BASIS_CONFIDENCE_MODE) {
				minTextField.setText(""+rulesBasis.getMinConfidence());
			} else if (mode == INTENTS_BASIS_SUPPORT_MODE) {
				minTextField.setText(""+intentsBasis.getMinSupport());
			}
			minTextField.setPreferredSize(new java.awt.Dimension(30,20));
		}
		return minTextField;
	}
	/**
	 * This method initializes maxTextField	
	 * 	
	 * @return javax.swing.JTextField	
	 */    
	private JTextField getMaxTextField() {
		if (maxTextField == null) {
			maxTextField = new JTextField();
			if (mode == RULES_BASIS_SUPPORT_MODE) {
				maxTextField.setText(""+rulesBasis.getMaxSupport());
			} else if (mode == RULES_BASIS_CONFIDENCE_MODE) {
				maxTextField.setText(""+rulesBasis.getMaxConfidence());
			} else if (mode == INTENTS_BASIS_SUPPORT_MODE) {
				maxTextField.setText(""+intentsBasis.getMaxSupport());
			}
			maxTextField.setPreferredSize(new java.awt.Dimension(30,20));
		}
		return maxTextField;
	}
      }
