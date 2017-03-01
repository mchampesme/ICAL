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

package lattice.gui.controller;

import java.awt.event.ActionEvent;
import java.util.Vector;

import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;

import lattice.algorithm.LatticeAlgorithm;
import lattice.algorithm.LatticeAlgorithmInc;
import lattice.algorithm.task.LatticeAlgorithmTask;
import lattice.gui.RelationalContextEditor;
import lattice.iceberg.algorithm.BordatIceberg;
import lattice.iceberg.algorithm.MagaliceA;
import lattice.iceberg.algorithm.MagaliceAGen;
import lattice.iceberg.algorithm.MagaliceO;
import lattice.iceberg.algorithm.Titanic;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.relation.ScalingBinaryRelation;


/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */

public class IcebergController
extends AbstractController {

		private JMenu menuIceberg = null;
		private JMenuItem algoMagalice = null;
		private JMenuItem algoBordatIceberg = null;
		private JMenuItem algoAttincre = null;
		private JMenuItem algoTitanic = null;

		private LatticeAlgorithmTask theTask=null;

		/**
		 * @param rce
		 */
		public IcebergController(RelationalContextEditor rce) {
			super(rce);
			initMenu();
			theTask=new LatticeAlgorithmTask(rce);
		}

		public void initMenu(){
			
			menuIceberg = new JMenu("Iceberg Lattice");
			menuIceberg.setMnemonic('I');

			// Les Items
			algoBordatIceberg = new JMenuItem("Bordat Iceberg");
			algoBordatIceberg.setMnemonic('B');
			algoBordatIceberg.addActionListener(this);
			menuIceberg.add(algoBordatIceberg);
			
			algoMagalice = new JMenuItem("Magalice");
			algoMagalice.setMnemonic('M');
			algoMagalice.addActionListener(this);
			menuIceberg.add(algoMagalice);
			
			algoAttincre = new JMenuItem("Attribute_Incremental");
			algoAttincre.setMnemonic('A');
			algoAttincre.addActionListener(this);
			menuIceberg.add(algoAttincre);
			
			algoTitanic = new JMenuItem("Titanic");
			algoTitanic.setMnemonic('T');
			algoTitanic.addActionListener(this);
			menuIceberg.add(algoTitanic);


		}

		public JMenu getMainMenu(){
			return menuIceberg;
		}


		/* (non-Javadoc)
		 * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
		 */
		public void actionPerformed(ActionEvent arg0) {
			String numString=null;
			double minsup = -1.0;
			numString = selectMinSupp();
			
			if (numString == null){
			}
			else
				minsup = Double.parseDouble(numString);
				
			if(arg0.getSource()==algoMagalice){
				//String numString=null;
				/*double minsup = -1.0;
				do{
					// Demander un support minimum 
					numString = JOptionPane.showInputDialog(rce, "Give a minimum support number");
					if(numString!=null){
						if(!numString.equals("")){
							try {
								minsup = Double.parseDouble(numString);
							} catch (NumberFormatException nfe) {
								minsup = -1d;
							}
						}
						if (numString.equals("") || minsup < 0d || minsup > 1d) {
							JOptionPane.showMessageDialog(rce,"The input should be : 0 <= minsup <= 1");
						}				
					}
				}
				while (numString!=null && (numString.equals("") || minsup < 0d || minsup > 1d));
				*/
				
				//if (numString == null)
					//addMessage("Algorithm \"Magalice\" canceled !\n");
				//else {
					LatticeAlgorithm algo =
						new MagaliceO(((MatrixBinaryRelationBuilder)rce.getSelectedRelation()),
							minsup);
					execAlgorithm(algo);

				//}
			}
			if(arg0.getSource()==algoBordatIceberg){
				// minsupp=0.30 to change later
				//String numString=null;
				//double minsup = -1.0;
				/*do{
					// Demander un support minimum 
					numString = JOptionPane.showInputDialog(rce, "Give a minimum support value");
					if(numString!=null){
						if(!numString.equals("")){
							try {
								minsup = Double.parseDouble(numString);
							} catch (NumberFormatException nfe) {
								minsup = -1d;
							}
						}
						if (numString.equals("") || minsup < 0d || minsup > 1d) {
							JOptionPane.showMessageDialog(rce,"The input should be : 0 <= minsup <= 1");
						}				
					}
				}
				while (numString!=null && (numString.equals("") || minsup < 0d || minsup > 1d));
				
				if (numString == null)
					addMessage("Algorithm \"BordatIceberg\" canceled !\n");
				else {*/
					LatticeAlgorithm algo =
						new BordatIceberg(((MatrixBinaryRelationBuilder)rce.getSelectedRelation()),
							minsup);
					execAlgorithm(algo);

				//}
			}
			
			if(arg0.getSource()==algoAttincre){
				  LatticeAlgorithmInc algo;

				  JFrame frame = new JFrame();
				  int choix = JOptionPane.showConfirmDialog(frame,
					  "Do you want the generators to be calculated ?",
					  "Generators Choice",
					  JOptionPane.YES_NO_OPTION);
								
				  if (choix == JOptionPane.YES_OPTION)
				  {
					  algo = new MagaliceAGen(((MatrixBinaryRelationBuilder)rce.getSelectedRelation()),
						  minsup);
				  }
				  else
					  algo = new MagaliceA(((MatrixBinaryRelationBuilder)rce.getSelectedRelation()),
						  minsup);
								
				  execAlgorithm(algo);
			  }

		     
						
			if(arg0.getSource()==algoTitanic){
					LatticeAlgorithm algo =
						new Titanic(((MatrixBinaryRelationBuilder)rce.getSelectedRelation()),
							minsup);
					execAlgorithm(algo);

			}
			
			rce.checkPossibleActions();
		}

		protected void execAlgorithm(LatticeAlgorithm algo){
			rce.setWorkOnRelation(algo.getBinaryRelation()); // marquer la relation 'On Use'
			Vector binRelOnUse=new Vector();
			binRelOnUse.add(algo.getBinaryRelation());
			theTask.setBinRelOnUse(binRelOnUse);
			theTask.setAlgo(algo);
			theTask.exec();
		}



		public void checkPossibleActions(){

			if(rce.getFamilyContexts().size()==0){
				menuIceberg.setEnabled(false);
				return;
			}

			RelationBuilder absRel=rce.getSelectedRelation();

			if(absRel instanceof MatrixBinaryRelationBuilder){
				menuIceberg.setEnabled(true);
				if(rce.isOnWork(absRel)) menuIceberg.setEnabled(false);
				return;
			}

			if(absRel instanceof ScalingBinaryRelation){
				menuIceberg.setEnabled(false);
				return;
			}

			if(absRel instanceof InterObjectBinaryRelation){
				menuIceberg.setEnabled(false);
				return;
			}
		}
		
		public String selectMinSupp(){
		String numString=null;
					double minsup = -1.0;
					do{
						// Demander un support minimum 
						numString = JOptionPane.showInputDialog(rce, "Give a minimum support number");
						if(numString!=null){
							if(!numString.equals("")){
								try {
									minsup = Double.parseDouble(numString);
								} catch (NumberFormatException nfe) {
									minsup = -1d;
								}
							}
							if (numString.equals("") || minsup < 0d || minsup > 1d) {
								JOptionPane.showMessageDialog(rce,"The input should be : 0 <= minsup <= 1");
							}				
						}
					}
					while (numString!=null && (numString.equals("") || minsup < 0d || minsup > 1d));
		return (numString);
		}
	}