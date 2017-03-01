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
 * Created on 9 juil. 2003
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package lattice.gui.dialog;

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Vector;

import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.ListSelectionModel;

import lattice.gui.OpenFileFrame;
import lattice.gui.RelationalContextEditor;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.RelationalContextFamily;

/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ExportDialogSelection
	extends JDialog
	implements ActionListener {

	public static int EXPORT=1;
	public static int CANCELLED=-1;
	private int Status=0;

	private JList theList = new JList();
	Vector listAll=new Vector();
	Vector listBin=new Vector();
	Vector listMvc=new Vector();
	Vector listLat=new Vector();

	private JButton cancelButton=new JButton("Cancel");
	private JButton exportButton=new JButton("Export");
	
	private JComboBox combo=null;
	
	private Object data=null;
	private int typeOfExport=OpenFileFrame.FAMILY_DATA;

	private RelationalContextEditor controler=null;

	/**
	 * @throws java.awt.HeadlessException
	 */
	public ExportDialogSelection(RelationalContextFamily relCtx, RelationalContextEditor controler) {
		super();
		
		this.controler=controler;
				
		for(int i=0;i<relCtx.size();i++){
			listAll.add(relCtx.get(i));
			if( relCtx.get(i).getClass().getName().endsWith("MatrixBinaryRelationBuilder")) listBin.add(relCtx.get(i));
			if( relCtx.get(i).getClass().getName().endsWith("MultiValuedRelation")) listMvc.add(relCtx.get(i));
			if( relCtx.get(i).getLattice()!=null) listLat.add(relCtx.get(i));
		}
		theList.setListData(listAll);
		theList.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);
		
		JPanel panelGlob=new JPanel(new BorderLayout());
		
		JPanel panelNorth = new JPanel(new FlowLayout());
		JLabel lab1=new JLabel("Select type of export :");
		panelNorth.add(lab1);
		combo=new JComboBox();
		combo.addItem("Relational Contexts Family");
		combo.addItem("Binary Relation");
		combo.addItem("Multi-Valued Relation");
		combo.addItem("Lattice");
		combo.addItem("Description logics KB");
		combo.addActionListener(this);
		panelNorth.add(combo);
		panelGlob.add(panelNorth,BorderLayout.NORTH);

		JPanel panelCenter=new JPanel(new BorderLayout());
		JLabel lab2=new JLabel("Then select data to export :");
		panelCenter.add(lab2,BorderLayout.NORTH);
		JScrollPane scp = new JScrollPane(theList, JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		panelCenter.add(scp,BorderLayout.CENTER);
		panelGlob.add(panelCenter,BorderLayout.CENTER);						
				
		JPanel panelSud=new JPanel(new FlowLayout());
		panelSud.add(exportButton);
		panelSud.add(cancelButton);
		exportButton.addActionListener(this);
		cancelButton.addActionListener(this);
		panelGlob.add(panelSud,BorderLayout.SOUTH);
		
		setContentPane(panelGlob);
		setTitle("Data Export Selection");
		setSize(400,400);
		setResizable(false);
		setModal(true);
	}

	/**
	 * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
	 */
	public void actionPerformed(ActionEvent arg0) {
		if(arg0.getSource()==combo){
			switch (combo.getSelectedIndex()) {
				case 0 :
					theList.setListData(listAll);
					theList.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);
					typeOfExport=OpenFileFrame.FAMILY_DATA;
					break;

				case 1 :
					theList.setListData(listBin);
					theList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
					typeOfExport=OpenFileFrame.BINARY_DATA;
					break;

				case 2 :
					theList.setListData(listMvc);
					theList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
					typeOfExport=OpenFileFrame.MULTI_VALUE_DATA;
					break;

				case 3 :
					theList.setListData(listLat);
					theList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
					typeOfExport=OpenFileFrame.LATTICE_DATA;
				break;
				
				case 4 :
					theList.setListData(listLat);
					theList.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);
					typeOfExport=OpenFileFrame.KRSS_DATA;
				break;
			}
			theList.repaint();
		}
		if(arg0.getSource()==exportButton){
			if((getTypeOfExport()==OpenFileFrame.FAMILY_DATA)||(getTypeOfExport()==OpenFileFrame.KRSS_DATA)){
				RelationalContextFamily rc=new RelationalContextFamily();
				for(int i=0;i<theList.getSelectedValues().length;i++){
					rc.add((RelationBuilder)theList.getSelectedValues()[i]);
				}
				data=rc;
			} else if(getTypeOfExport()==OpenFileFrame.LATTICE_DATA) {
				data=((RelationBuilder)theList.getSelectedValue()).getLattice();
			} else {
				data=theList.getSelectedValue();
			}
			Status=EXPORT;
			dispose();
		}
		if(arg0.getSource()==cancelButton){
			Status=CANCELLED;
			dispose();
		}
	}

	public void askParameter(){
		if(controler!=null) controler.setEnabled(false);
		show();
		if(controler!=null) controler.setEnabled(true);
	}
	
	public int getTypeOfExport(){
		return typeOfExport;
	}

	public Object getData(){
		return data;
	}
	
	public int getAction(){
		return Status;
	}
}
