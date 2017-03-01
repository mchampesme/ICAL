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
package rule.gui;

import java.util.Vector;

import javax.swing.JCheckBox;
import javax.swing.JFrame;

import lattice.alpha.util.BGIntent;
import lattice.gui.RelationalContextEditor;
import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import rule.util.IntentsBasis;
import rule.util.RulesBasis;
/**
 * A Swing GUI to filter premise and consequence values for the rules basis visualization 
 * @author Manuel Aupetit
 */
public class AttributesFilter extends JFrame {	
	private javax.swing.JPanel jContentPane = null;

	private javax.swing.JCheckBox[] checkBoxes = null;
	private RulesBasis rulesBasis = null;
	private IntentsBasis intentsBasis = null;
	private RelationalContextEditor relCtxEd = null;
	private int mode = 0;
	
	public static final int PREMISE_MODE = 1;
	public static final int CONSEQUENCE_MODE = 2;
	public static final int INTENT_MODE = 3;

	private javax.swing.JScrollPane attributesScrollPane = null;
	private javax.swing.JPanel validationPanel = null;
	private javax.swing.JButton okButton = null;
	private javax.swing.JButton cancelButton = null;
	private javax.swing.JLabel attributesInstructionLabel = null;
	private javax.swing.JPanel attributesChoicePanel = null;
	

	/**
	 * 
	 * @param rulesBasis
	 * @param mode
	 * @param relCtxEd
	 */
	public AttributesFilter(RulesBasis rulesBasis, int mode, RelationalContextEditor relCtxEd) {
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
	public AttributesFilter(IntentsBasis intentsBasis, int mode, RelationalContextEditor relCtxEd) {
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
		this.setSize(400, 280);
		this.setContentPane(getJContentPane());
		this.getRootPane().setDefaultButton(getOkButton());
		this.setLocation(300, 100);
		this.setTitle("Select Attributes");
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
			jContentPane.add(getAttributesInstructionLabel(), java.awt.BorderLayout.NORTH);
			jContentPane.add(getAttributesScrollPane(), java.awt.BorderLayout.CENTER);
			jContentPane.add(getValidationPanel(), java.awt.BorderLayout.SOUTH);
		}
		return jContentPane;
	}
	/**
	 * This method initializes attributesScrollPane
	 * 
	 * @return javax.swing.JScrollPane
	 */
	private javax.swing.JScrollPane getAttributesScrollPane() {
		if(attributesScrollPane == null) {
			attributesScrollPane = new javax.swing.JScrollPane();
			attributesScrollPane.setViewportView(getAttributesChoicePanel());
		}
		return attributesScrollPane;
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

					Intent attributes = new BGIntent();
					for (int i=0; i<getCheckBoxes().length; i++) {
						if (getCheckBoxes()[i].isSelected()) {
							attributes.add(new DefaultFormalAttribute(getCheckBoxes()[i].getLabel()));
						}
					}
					if (mode == PREMISE_MODE) {
						new TableVisualization(rulesBasis.filterRulesByPremise(attributes), relCtxEd); 
					}
					else if (mode == CONSEQUENCE_MODE) {
						new TableVisualization(rulesBasis.filterRulesByConsequence(attributes), relCtxEd); 
					}
					else if (mode == INTENT_MODE) {
						new IntentsTableVisualization(intentsBasis.filterIntentsByAttributes(attributes), relCtxEd);
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
	 * This method initializes attributesInstructionLabel
	 * 
	 * @return javax.swing.JLabel
	 */
	private javax.swing.JLabel getAttributesInstructionLabel() {
		if(attributesInstructionLabel == null) {
			attributesInstructionLabel = new javax.swing.JLabel();
			attributesInstructionLabel.setText("Select only the attributes you want to discard:");
			attributesInstructionLabel.setVerticalAlignment(javax.swing.SwingConstants.BOTTOM);
			attributesInstructionLabel.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
			attributesInstructionLabel.setVerticalTextPosition(javax.swing.SwingConstants.BOTTOM);
			attributesInstructionLabel.setPreferredSize(new java.awt.Dimension(228,35));
			attributesInstructionLabel.setMaximumSize(new java.awt.Dimension(228,35));
			attributesInstructionLabel.setMinimumSize(new java.awt.Dimension(228,35));
		}
		return attributesInstructionLabel;
	}
	/**
	 * This method initializes attributesChoicePanel
	 * 
	 * @return javax.swing.JPanel
	 */
	private javax.swing.JPanel getAttributesChoicePanel() {
		if(attributesChoicePanel == null) {
			attributesChoicePanel = new javax.swing.JPanel();
			java.awt.GridBagConstraints consGridBagConstraints9 = new java.awt.GridBagConstraints();
			consGridBagConstraints9.gridx = 0;
			consGridBagConstraints9.anchor = java.awt.GridBagConstraints.WEST;
			attributesChoicePanel.setLayout(new java.awt.GridBagLayout());
			for (int i=0; i<getCheckBoxes().length; i++) {
				consGridBagConstraints9.gridy = i;
				attributesChoicePanel.add(getCheckBoxes()[i], consGridBagConstraints9);
			}
		}
		return attributesChoicePanel;
	}

	private javax.swing.JCheckBox[] getCheckBoxes() {
		if (checkBoxes == null) {
			Intent attributes = null;
			if (mode == PREMISE_MODE) {
				attributes = rulesBasis.getPremiseAttributes();
			}
			else if (mode == CONSEQUENCE_MODE) {
				attributes = rulesBasis.getConsequenceAttributes();
			}
			else if (mode == INTENT_MODE) {
				attributes = intentsBasis.getAttributes();
			}
			checkBoxes = new JCheckBox[attributes.size()];
			int i = 0;
			for (FormalAttribute attr : attributes) {
				checkBoxes[i] = new JCheckBox(attr.toString());
				i++;
			}
		}
		return checkBoxes;
	}
}
