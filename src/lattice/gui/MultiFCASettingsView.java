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


package lattice.gui;
import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.GridLayout;
import java.awt.Insets;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.util.Vector;

import javax.swing.Box;
import javax.swing.ButtonGroup;
import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.ListSelectionModel;
import javax.swing.border.LineBorder;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.relation.RelationalContextFamily;

/**
 * @author rouanehm
 * Created on 28-Apr-2004
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */

public class MultiFCASettingsView extends JDialog implements ActionListener, ListSelectionListener {

	private static int WIDE_ENCODING=0;
	private static int NARROW_ENCODING=1;
	private static int LATTICE_ENCODING=0;
	private static int GSH_ENCODING=1;	
	
	// lattice labeling settings
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
	
	// relational context family
	private RelationalContextFamily rcf=null;
	private static Vector contextNames;
	private static Vector selectedContexts=new Vector();
	
	private static Vector relAttributeNames;
	private static Vector selectedRelAttributes=new Vector();
	private static String selectedInitialContext;

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
	
	
	private JList contextsList=null;
	private JList relAttributesList=null;
	private JList initialContextsList=null;
	
	private DefaultListModel ovaNamesListModel=null;
	private DefaultListModel initialCtxNamesListModel=null;
	
	private JPanel contextsSeletionPanel=new JPanel(new BorderLayout());
	private JPanel relAttrSeletionPanel=new JPanel(new BorderLayout());
	private JPanel initialContextSeletionPanel=new JPanel(new BorderLayout());

	public MultiFCASettingsView(RelationalContextFamily relCtx) {
		super();
		rcf=relCtx;
		
		JTabbedPane tabbedPane = new JTabbedPane();	
		tabbedPane.addTab("RCF selection",createCtxSelectionPanel());
		tabbedPane.setMnemonicAt(0, KeyEvent.VK_1);

		tabbedPane.addTab("OVA selection", createOVASelectionPanel());
		tabbedPane.setMnemonicAt(1, KeyEvent.VK_2);

		tabbedPane.addTab("Initial context", createInitialCtxSeclectionPanel());
		tabbedPane.setMnemonicAt(2, KeyEvent.VK_3);

		tabbedPane.addTab("Encoding", createEncodingSelectionPanel());
		tabbedPane.setMnemonicAt(3, KeyEvent.VK_4);
        
		tabbedPane.addTab("Labeling", createLabelingSelectionPanel());
		tabbedPane.setMnemonicAt(4, KeyEvent.VK_5);
		
		JPanel Validationpanel = new JPanel(new FlowLayout());		
		cancelButton.addActionListener(this);
		fireButton.addActionListener(this);
		fireButton.setEnabled(false);
		Validationpanel.add(fireButton);
		Validationpanel.add(cancelButton);
		        
		// Add the tabbed pane and validationPanel to DJialog panel.
		//getContentPane().setLayout(new GridLayout());
		getContentPane().add(tabbedPane,BorderLayout.CENTER);
		getContentPane().add(Validationpanel,BorderLayout.SOUTH);
        
		//Uncomment the following line to use scrolling tabs.
		//tabbedPane.setTabLayoutPolicy(JTabbedPane.SCROLL_TAB_LAYOUT);
		setTitle("Multi-FCA algorithm settings");
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

	private JPanel createCtxSelectionPanel() {	
		fillContextNamesVector();	
		contextsList=new JList(contextNames);
		contextsList.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);
		contextsList.addListSelectionListener((ListSelectionListener) this);
		contextsList.clearSelection();
		JScrollPane jsp = new JScrollPane(contextsList, JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		contextsSeletionPanel=new JPanel(new BorderLayout());		 		
		contextsSeletionPanel.add(jsp,BorderLayout.CENTER);
		contextsSeletionPanel.setLayout(new GridLayout(1, 1));
		return contextsSeletionPanel;
	}

	/**
	 * @return
	 */
	private JPanel createOVASelectionPanel() {
		ovaNamesListModel = new DefaultListModel();
		fillOvaNamesListModel();
		relAttributesList=new JList(ovaNamesListModel);
		relAttributesList.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);
		relAttributesList.addListSelectionListener(this);			
		relAttributesList.clearSelection();
		JScrollPane jsp = new JScrollPane(relAttributesList, JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		relAttrSeletionPanel=new JPanel(new BorderLayout());		 		
		relAttrSeletionPanel.add(jsp,BorderLayout.CENTER);
		relAttrSeletionPanel.setLayout(new GridLayout(1, 1));
		return relAttrSeletionPanel;
	}

	/**
	 * @return
	 */
	private JPanel createInitialCtxSeclectionPanel() {
		initialCtxNamesListModel = new DefaultListModel();
		fillInitialCtxNamesListModel();
		initialContextsList=new JList(initialCtxNamesListModel);
		initialContextsList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
		initialContextsList.addListSelectionListener(this);	
		initialContextsList.clearSelection();
		JScrollPane jsp = new JScrollPane(initialContextsList, JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		initialContextSeletionPanel=new JPanel(new BorderLayout());		
		initialContextSeletionPanel.add(jsp,BorderLayout.CENTER);
		return initialContextSeletionPanel;
	}

	/**
	 * @return
	 */
	private JPanel createEncodingSelectionPanel() {		
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
		
		// create a horizontal box and put the entree, condiments, and
	    // placeOrderPanels in it
		Box orderBox = Box.createVerticalBox();
		orderBox.add(structPanel);
		orderBox.add(schemaPanel);
		// create the panel for this tabbed component and set the layout 
		JPanel panel = new JPanel(new BorderLayout());
		// add the components to the panel and return the panel
		panel.add(orderBox, BorderLayout.CENTER);
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
		
	public static boolean getSettings(RelationalContextFamily relCtx, RelationalContextEditor controler){
		if(controler!=null) controler.setEnabled(false);
		MultiFCASettingsView settingsView = new MultiFCASettingsView(relCtx);
		//settingsView.show();
		if(controler!=null) controler.setEnabled(true);
		return exitStatus == TERMINATED;		
	}

	/* (non-Javadoc)
	 * @see javax.swing.event.ListSelectionListener#valueChanged(javax.swing.event.ListSelectionEvent)
	 */
	public void valueChanged(ListSelectionEvent arg0) {
		if(arg0.getSource()==contextsList){
			selectedContexts.removeAllElements();
			//System.out.println("Selection of new contexts in RCF...");
			if(contextsList.getSelectedIndex()!=-1){
				for(int i=0;i<contextsList.getSelectedValues().length;i++){
					selectedContexts.add(contextsList.getSelectedValues()[i].toString());
				}
				fireButton.setEnabled(true);

			}
			// update List Model for OVA selection panel
			ovaNamesListModel.removeAllElements();
			fillOvaNamesListModel();
			relAttributesList.clearSelection();
			// update List Model for initial ctx selection panel
			initialCtxNamesListModel.removeAllElements();
			fillInitialCtxNamesListModel();
			initialContextsList.clearSelection();
		}

		if(arg0.getSource()==relAttributesList){
			selectedRelAttributes.removeAllElements();
			//System.out.println("Selection of new relational attributes...");
			if(contextsList.getSelectedIndex()!=-1){
				for(int i=0;i<relAttributesList.getSelectedValues().length;i++){
					selectedRelAttributes.add(relAttributesList.getSelectedValues()[i].toString());
				}
			}
		}
		
		if(arg0.getSource()==initialContextsList){
			//System.out.println("assign a new value to initial context...");
			selectedInitialContext=initialContextsList.getSelectedValue().toString();
		} 					
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
			if(selectedInitialContext!=null){
				exitStatus=TERMINATED;		
				hide();		
				dispose();			
			}
			else{
				Toolkit.getDefaultToolkit().beep();
				JOptionPane.showMessageDialog(this,"You must choose an initial context");
			}
		}//if		
		if(arg0.getSource()==cancelButton){
			exitStatus=CANCELLED;
			hide();
			dispose();
		}						
	}
	/**
	 * 
	 */
	private void fillContextNamesVector() {
		contextNames=new Vector();
		for(int i=0;i<rcf.size();i++){
			if( rcf.get(i) instanceof MatrixBinaryRelationBuilder
				&& !(rcf.get(i) instanceof InterObjectBinaryRelation)) 
			contextNames.add(rcf.get(i));}		
	}

	private void fillOvaNamesListModel(){		
		for(int i=0;i<selectedContexts.size();i++){
			String ctxName=selectedContexts.elementAt(i).toString();
			for(int j=0;j<rcf.size();j++){
				if(rcf.get(j) instanceof InterObjectBinaryRelation){
					InterObjectBinaryRelation ova =(InterObjectBinaryRelation) rcf.get(j);
					if(ova.getAttributesContextName().equals(ctxName)) 
						ovaNamesListModel.addElement(ova.getName());  
				}
			}
		}
	}	
	
	private void fillInitialCtxNamesListModel(){
		for(int i=0;i<selectedContexts.size();i++){
			String ctxName=selectedContexts.elementAt(i).toString();
			initialCtxNamesListModel.addElement(ctxName);  
		}
	}
	public static void useUMLSettings(){
		
		selectedContexts.add("Classes");
		selectedContexts.add("Relations");
		selectedRelAttributes.add("outgoing");
		selectedRelAttributes.add("incoming");
		selectedRelAttributes.add("source");
		selectedRelAttributes.add("target");
		selectedInitialContext = new String("Relations");
		exitStatus=TERMINATED;
	}

	public static void displayRCFSettings(){
		if(getExitStatus()==-1){
			System.out.println("RCF Processing cancelled...!\n");
			return;
		}
		else{
			System.out.println("Input settings are: ");
			System.out.println("Selected contexts:");
			for(int i=0;i<getSelectedContexts().size();i++){
				System.out.println(getSelectedContexts().elementAt(i));
			}
			System.out.println("Selected relational (object-valued) attributes:");
			for(int i=0;i<getSelectedRelAttributes().size();i++){
				System.out.println(getSelectedRelAttributes().elementAt(i));
			}
			System.out.print("Selected initial context: ");
			System.out.println(getSelectedInitalContext());
		}		
	}
	
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
		}		
	}

	public static void displayLabelingSettings(){
		if(getExitStatus()==-1){
			System.out.println("RCF Processing cancelled...!\n");
			return;
		}
		else{			
			System.out.print("Fundamental labeling preference is: ");
			if(getSelectedfundamentalLabeling()==FFL)
				System.out.println("FULL LABELING");		
			else System.out.println("REDUCED LABELING");

			System.out.print("Relational labeling preference is: ");
			if(getSelectedRelationalLabeling()==FRL)
				System.out.println("FULL LABELING");		
			else System.out.println("REDUCED LABELING");
		}		
	}
	
	public static int getExitStatus(){ 
		return exitStatus;
	}
	public static Vector getSelectedContexts() {
			return selectedContexts;
	}

	public static Vector getSelectedRelAttributes() {
			return selectedRelAttributes;
	}

	public static String getSelectedInitalContext() {
			return selectedInitialContext;
	}
	public static int getSelectedEncodingStructure(){	
		return encodingStruct;
	}
	public static int getSelectedEncodingSchema(){	
		return encodingSchema;
	}
	
	public static int getSelectedfundamentalLabeling(){
			return fundamentalLabeling;
		}
	public static int getSelectedRelationalLabeling(){
		return relationalLabeling;
	}	
	public static int getTerminatedStatus(){
		return TERMINATED;
	}

	/**
	 * @param i
	 */
	public static void setEncodingStructure(int struct) {
		encodingStruct = struct;
	}

	/**
	 * @param i
	 */
	public static void setEncodingSchema(int schema) {
		encodingSchema=schema;		
	}

	public static void setFundamentalLabeling(int labeling) {
		fundamentalLabeling=labeling;
	}
	public static void setRelationalLabeling(int labeling) {
		relationalLabeling=labeling;
	}
	/**
	 * @return
	 */
	public static boolean checkUMLFormat(RelationalContextFamily rcf) {
		if(rcf.getForName("Classes")==null) return false;
		if(rcf.getForName("Relations")==null) return false;
		if(rcf.getForName("outgoing")==null) return false;
		if(rcf.getForName("incoming")==null) return false;
		if(rcf.getForName("source")==null) return false;
		if(rcf.getForName("target")==null) return false;
		return true;
	}
	public static int getFullFundamentalLabeling(){
		return FFL; 
	}
	public static int getReducedFundamentalLabeling(){
		return RFL; 
	}
	public static int getFullRelationalLabeling(){
		return FRL; 
	}
	public static int getReducedRelationalLabeling(){
		return RRL; 
	}	
}

