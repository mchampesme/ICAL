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
 * Created on 2004-06-10
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package lattice.gui;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Insets;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;

import javax.swing.Box;
import javax.swing.ButtonGroup;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JTabbedPane;
import javax.swing.border.LineBorder;
import javax.swing.border.TitledBorder;


/**
 * @author rouanehm
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class UMLBatchSettingsView extends JDialog implements ActionListener {

	private static int WIDE_ENCODING=0;
	private static int NARROW_ENCODING=1;
	private static int LATTICE_ENCODING=0;
	private static int GSH_ENCODING=1;	
	
//	 lattice labeling settings
	private static int FFL=0;  // FULL FUNDAMENTAL LABELING
	private static int RFL=1;  // REDUCED FUNDAMENTAL LABELING
	
	private static int FRL=0; // FULL RELATIONAL LABELING
	private static int RRL=1; // REDUCED RELATIONAL LABELING
	
	// default encoding
	private static int encodingStruct=LATTICE_ENCODING;
	private static int encodingSchema=NARROW_ENCODING; 
	// default labeling
	private static int fundamentalLabeling=FFL;
	private static int relationalLabeling=FRL;
		
	private static int TERMINATED=2;
	private static int CANCELLED=-1;
	private static int exitStatus=0;
	
	private JButton cancelButton=new JButton("Cancel");
	private JButton fireButton=new JButton("Go");
	private JRadioButton latticeRadioButton = new JRadioButton("Complete lattice");
	private JRadioButton gshRadioButton = new JRadioButton("Galois-Sub-Hierarchy");
	private JRadioButton narrowRadioButton = new JRadioButton("Narrow encoding");
	private JRadioButton wideRadioButton = new JRadioButton("Wide encoding");

	// labeling preferences
	private JRadioButton fullFLRadioButton = new JRadioButton("Full");
	private JRadioButton reducedFLRadioButton = new JRadioButton("Reduced");
	private JRadioButton fullRLRadioButton = new JRadioButton("Full");
	private JRadioButton reducedRLRadioButton = new JRadioButton("Reduced");
		
	private static boolean reverseEncodingOption=false; // defautl value does not allow reverse encoding of UML model
	private JCheckBox reverseEncCheckBox = new JCheckBox("Reverse encoding UML model");
	private JCheckBox underConstCheckBox = new JCheckBox("Under-construction");

	public UMLBatchSettingsView() {
		super();
		
		JTabbedPane tabbedPane = new JTabbedPane();	
		tabbedPane.addTab("Encoding",createEncodingPanel());
		tabbedPane.setMnemonicAt(0, KeyEvent.VK_1);

		tabbedPane.addTab("Reverse encoding",createReverseEncodingPanel());
		tabbedPane.setMnemonicAt(1, KeyEvent.VK_2);
		
		tabbedPane.addTab("Labeling", createLabelingSelectionPanel());
		tabbedPane.setMnemonicAt(2, KeyEvent.VK_3);
        
		JPanel Validationpanel = new JPanel(new FlowLayout());		
		cancelButton.addActionListener(this);
		fireButton.addActionListener(this);
		//fireButton.setEnabled(false);
		Validationpanel.add(fireButton);
		Validationpanel.add(cancelButton);
		        
		// Add the tabbed pane and validationPanel to DJialog panel.
		//getContentPane().setLayout(new GridLayout());
		getContentPane().add(tabbedPane,BorderLayout.CENTER);
		getContentPane().add(Validationpanel,BorderLayout.SOUTH);
        
		//Uncomment the following line to use scrolling tabs.
		//tabbedPane.setTabLayoutPolicy(JTabbedPane.SCROLL_TAB_LAYOUT);
		setTitle("Multi-FCA batch algorithm settings for UML");
		// exit the application when the JDialog is closed
		//setDefaultCloseOperation(JDialog.EXIT_ON_CLOSE);
		// set the size of the 
		//setLocationRelativeTo(null);
		//setResizable(false);
		//setSize(300,150);
		setModal(true);
		
		int height = 300;
		int width = 450;
		// pack the frame to get correct insets
		pack();
		Insets fI = getInsets();
		setSize(width + fI.right + fI.left, height + fI.top + fI.bottom);
		// center the frame on screen
		Dimension sD = Toolkit.getDefaultToolkit().getScreenSize();
		setLocation((sD.width - width)/2, (sD.height - height)/2);
		// make the JDialog visible
		setVisible(true);
		//show();
	}
	/**
	 * @return
	 */
	private JPanel createEncodingPanel() {		
		// Register a listener for the radio buttons.
		latticeRadioButton.addActionListener(this);
		gshRadioButton.addActionListener(this);
		narrowRadioButton.addActionListener(this);
		wideRadioButton.addActionListener(this);
		latticeRadioButton.setSelected(true);
		narrowRadioButton.setSelected(true);
		
		// create and populate the encoding structure and set a border
		final JPanel structPanel = new JPanel();
		final ButtonGroup structGroup = new ButtonGroup();
		structPanel.add(latticeRadioButton);
		latticeRadioButton.setActionCommand("LATTICE");
		structGroup.add(latticeRadioButton);
		structPanel.add(gshRadioButton);
		gshRadioButton.setActionCommand("GSH");
		structGroup.add(gshRadioButton);
		structPanel.setBorder(new TitledBorder(new LineBorder(Color.black), 
		 "Encoding structure", TitledBorder.CENTER, TitledBorder.TOP));

		// create and populate the encoding schema and set a border
		final JPanel schemaPanel = new JPanel();
		final ButtonGroup schemaGroup = new ButtonGroup();
		schemaPanel.add(narrowRadioButton);
		narrowRadioButton.setActionCommand("NARROW");
		schemaGroup.add(narrowRadioButton);
		schemaPanel.add(wideRadioButton);
		wideRadioButton.setActionCommand("WIDE");
		schemaGroup.add(wideRadioButton);
		schemaPanel.setBorder(new TitledBorder(new LineBorder(Color.black), 
		 "Encoding schema", TitledBorder.CENTER, TitledBorder.TOP));
		
		// create a horizontal box and put the structure & schema panels in it
		Box orderBox = Box.createVerticalBox();
		orderBox.add(structPanel);
		orderBox.add(schemaPanel);
		// create the panel for this tabbed component and set the layout 
		JPanel panel = new JPanel(new BorderLayout());
		// add the components to the panel and return the panel
		panel.add(orderBox, BorderLayout.CENTER);
		return panel;
	}
	
	private JPanel createReverseEncodingPanel(){
		
		// Register a listener for the radio buttons.
		reverseEncCheckBox.addActionListener(this);
		underConstCheckBox.addActionListener(this);
		
		// create and populate the reverse encoding panel and set a border
		final JPanel reverseEncPanel = new JPanel();
		reverseEncPanel.add(reverseEncCheckBox);
		reverseEncPanel.add(underConstCheckBox);
		reverseEncPanel.setBorder(new TitledBorder(new LineBorder(Color.black), 
				 "Reverse encoding", TitledBorder.CENTER, TitledBorder.TOP));
		// create a horizontal box and put the reverse encoding panel in it
		Box reverseEncBox = Box.createVerticalBox();
		reverseEncBox.add(reverseEncPanel);
	
		// create the panel for this tabbed component and set the layout 
		JPanel panel = new JPanel(new BorderLayout());
		// add the components to the panel and return the panel
		panel.add(reverseEncBox, BorderLayout.CENTER);
		return panel;
	}

	private JPanel createLabelingSelectionPanel() {		
		// Register a listener for the radio buttons.
		fullFLRadioButton.addActionListener(this);
		reducedFLRadioButton.addActionListener(this);
		fullRLRadioButton.addActionListener(this);
		reducedRLRadioButton.addActionListener(this);
		// initial stutus
		fullFLRadioButton.setSelected(true);
		fullRLRadioButton.setSelected(true);
		
		// create and populate the fundamental labeling and set a border
		final JPanel fundamentalLabelingPanel = new JPanel();
		final ButtonGroup fundamentalLabelingGroup = new ButtonGroup();
		fundamentalLabelingPanel.add(fullFLRadioButton);
		fullFLRadioButton.setActionCommand("Full");
		fundamentalLabelingGroup.add(fullFLRadioButton);
		fundamentalLabelingPanel.add(reducedFLRadioButton);
		reducedFLRadioButton.setActionCommand("Reduced");
		fundamentalLabelingGroup.add(reducedFLRadioButton);
		fundamentalLabelingPanel.setBorder(new TitledBorder(new LineBorder(Color.black), 
		 "Fundamental labeling", TitledBorder.CENTER, TitledBorder.TOP));

		// create and populate the relational labeling and set a border
		final JPanel relationalLabelingPanel = new JPanel();
		final ButtonGroup relationalLabelingGroup = new ButtonGroup();
		relationalLabelingPanel.add(fullRLRadioButton);
		fullRLRadioButton.setActionCommand("Full");
		relationalLabelingGroup.add(fullRLRadioButton);
		relationalLabelingPanel.add(reducedRLRadioButton);
		reducedRLRadioButton.setActionCommand("Reduced");
		relationalLabelingGroup.add(reducedRLRadioButton);
		relationalLabelingPanel.setBorder(new TitledBorder(new LineBorder(Color.black), 
		 "Relational labeling", TitledBorder.CENTER, TitledBorder.TOP));

		 
		// create a horizontal box and put the entree, condiments, and
	    // placeOrderPanels in it
		Box orderBox = Box.createVerticalBox();
		orderBox.add(fundamentalLabelingPanel);
		orderBox.add(relationalLabelingPanel);
		// create the panel for this tabbed component and set the layout 
		JPanel panel = new JPanel(new BorderLayout());
		// add the components to the panel and return the panel
		panel.add(orderBox, BorderLayout.CENTER);
		return panel;
	}	
	
	public static boolean getSettings(RelationalContextEditor controler){
		if(controler!=null) controler.setEnabled(false);
		UMLBatchSettingsView settingsView = new UMLBatchSettingsView();
		//settingsView.show();
		if(controler!=null) controler.setEnabled(true);
		return exitStatus == TERMINATED;		
	}
	 
	/* (non-Javadoc)
	 * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
	 */
	public void actionPerformed(ActionEvent arg0) {
		if(arg0.getSource()==latticeRadioButton){
			encodingStruct=LATTICE_ENCODING;
		}
		if(arg0.getSource()==gshRadioButton){
			Toolkit.getDefaultToolkit().beep();
			JOptionPane.showMessageDialog(this,"Option not available yet, the complete lattice will be used");
			//encodingStruct=GSH_ENCODING;
			encodingStruct=LATTICE_ENCODING;
			latticeRadioButton.setSelected(true);
		}
		if(arg0.getSource()==narrowRadioButton){
			encodingSchema=NARROW_ENCODING;
		}
		if(arg0.getSource()==wideRadioButton){
			encodingSchema=WIDE_ENCODING;
		}
		if(arg0.getSource()==reverseEncCheckBox){
			reverseEncodingOption=reverseEncCheckBox.isSelected();
		}
		if(arg0.getSource()==fullFLRadioButton){
			fundamentalLabeling=FFL;
		}
		if(arg0.getSource()==reducedFLRadioButton){
			fundamentalLabeling=RFL;
		}
		if(arg0.getSource()==fullRLRadioButton){
			relationalLabeling=FRL;
		}
		if(arg0.getSource()==reducedRLRadioButton){
			relationalLabeling=RRL;
		}				
		if(arg0.getSource()==fireButton){
				exitStatus=TERMINATED;		
				hide();		
				dispose();			
		}		
		if(arg0.getSource()==cancelButton){
			exitStatus=CANCELLED;
			hide();
			dispose();
		}						
	}
	/**
	 * 
	 */
	public static void displayEncodingSettings(){
		if(getExitStatus()==-1){
			System.out.println("RCF Processing cancelled...!\n");
			return;
		}
		else{			
			System.out.print("Selected encoding structure: ");
			if(getSelectedEncodingStructure()==LATTICE_ENCODING)
				System.out.println("LATTICE_ENCODING");		
			else System.out.println("GSH_ENCODING");

			System.out.print("Selected encoding schema: ");
			if(getSelectedEncodingSchema()==NARROW_ENCODING)
				System.out.println("NARROW_ENCODING");		
			else System.out.println("WIDE_ENCODING");
			
			System.out.print("Reverse encoding of UML model is required: ");
			if(reverseEncodingOption)
				System.out.println("YES");		
			else System.out.println("NO");
		}		
	}
	
	public static void displayLabelingSettings(){
		if(getExitStatus()==-1){
			System.out.println("RCF Processing cancelled...!\n");
			return;
		}
		else{			
			System.out.print("Fundamental labeling preference is: ");
			if(getFundamentalLabeling()==FFL)
				System.out.println("FULL LABELING");		
			else System.out.println("REDUCED LABELING");

			System.out.print("Relational labeling preference is: ");
			if(getRelationalLabeling()==FRL)
				System.out.println("FULL LABELING");		
			else System.out.println("REDUCED LABELING");
		}		
	}
	
	
	public static int getExitStatus(){ 
		return exitStatus;
	}
	public static int getSelectedEncodingStructure(){	
		return encodingStruct;
	}
	public static int getSelectedEncodingSchema(){	
		return encodingSchema;
	}
	public static int getTerminatedStatus(){
		return TERMINATED;
	}
	/**
	 * 
	 */
	public static int getEncodingStructure() {
		return encodingStruct;		
	}
	/**
	 * 
	 */
	public static int getEncodingSchema() {
		return encodingSchema;		
	}
	public static int getFundamentalLabeling() {
		return fundamentalLabeling;
		
	}
	public static int getRelationalLabeling() {
		return relationalLabeling;		
	}	
}

