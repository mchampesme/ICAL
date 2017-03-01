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
 * Created on 2004-08-11
 * @author Manuel Aupetit
 */
package lattice.database.gui;

import java.awt.event.ActionEvent;

import javax.swing.JMenu;
import javax.swing.JMenuItem;

import lattice.database.util.DatabaseConnection;
import lattice.database.util.DatabaseFunctions;
import lattice.database.util.DatabaseManagement;
import lattice.gui.RelationalContextEditor;
import lattice.gui.controller.AbstractController;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.relation.ScalingBinaryRelation;
import rule.gui.IntentsTableVisualization;
import rule.util.IntentsBasis;

/**
 * A controller for the database to use in the Relational Context Editor 
 * @author Manuel Aupetit
 */
public class DatabaseController extends AbstractController {
	
	private DatabaseManagement dbm = null;
	
	private JMenu databaseMenu = null;
	
	private JMenu contextsMenu = null;
	private JMenuItem saveFamilyItem = null;
	private JMenuItem loadFamilyItem = null;
	private JMenuItem deleteContextsItem = null;
	
	private JMenu rulesBasisMenu = null;
	private JMenuItem viewAssociatedRulesBasisItem = null;
	private JMenuItem deleteRulesBasisItem = null;
	private JMenuItem exportAssociatedRulesBasisToXMLItem = null;
	
	private JMenu latticesMenu = null;
	private JMenuItem saveAssociatedLatticeItem = null;
	private JMenuItem viewAssociatedLatticeItem = null;
	private JMenuItem deleteLatticesItem = null;
	private JMenuItem exportAssociatedLatticeToXMLItem = null;
	private JMenuItem viewIntentsItem = null;
	
	private JMenu databaseManagementMenu = null;
	private JMenuItem deleteDatabaseItem = null;
	private JMenuItem sqlUpdateItem = null;
	private JMenuItem configureDatabaseItem = null;
	
	
	public DatabaseController(RelationalContextEditor relCtxEd) {
		super(relCtxEd);
		initMenu();
	}
	
	public void initMenu() {
		
		databaseMenu = new JMenu("Database");
		databaseMenu.setMnemonic('D');
		
		contextsMenu = new JMenu("Relational Contexts Family");
		saveFamilyItem = new JMenuItem("Save...");
		saveFamilyItem.addActionListener(this);
		contextsMenu.add(saveFamilyItem);
		loadFamilyItem = new JMenuItem("Load...");
		loadFamilyItem.addActionListener(this);
		contextsMenu.add(loadFamilyItem);
		deleteContextsItem = new JMenuItem("Delete...");
		deleteContextsItem.addActionListener(this);
		contextsMenu.add(deleteContextsItem);
		
		rulesBasisMenu = new JMenu("Rules Basis");
		viewAssociatedRulesBasisItem = new JMenuItem("View Associated...");
		viewAssociatedRulesBasisItem.addActionListener(this);
		rulesBasisMenu.add(viewAssociatedRulesBasisItem);
		deleteRulesBasisItem = new JMenuItem("Delete...");
		deleteRulesBasisItem.addActionListener(this);
		rulesBasisMenu.add(deleteRulesBasisItem);
		exportAssociatedRulesBasisToXMLItem = new JMenuItem("Export Associated to XML...");
		exportAssociatedRulesBasisToXMLItem.addActionListener(this);
		rulesBasisMenu.add(exportAssociatedRulesBasisToXMLItem);
		
		latticesMenu = new JMenu("Lattices");
		saveAssociatedLatticeItem = new JMenuItem("Save Associated");
		saveAssociatedLatticeItem.addActionListener(this);
		latticesMenu.add(saveAssociatedLatticeItem);
		viewAssociatedLatticeItem = new JMenuItem("View Associated...");
		viewAssociatedLatticeItem.addActionListener(this);
		latticesMenu.add(viewAssociatedLatticeItem);
		deleteLatticesItem = new JMenuItem("Delete...");
		deleteLatticesItem.addActionListener(this);
		latticesMenu.add(deleteLatticesItem);
		exportAssociatedLatticeToXMLItem = new JMenuItem("Export Associated to XML...");
		exportAssociatedLatticeToXMLItem.addActionListener(this);
		latticesMenu.add(exportAssociatedLatticeToXMLItem);
		viewIntentsItem = new JMenuItem("View Lattice Intents");
		viewIntentsItem.addActionListener(this);
		latticesMenu.add(viewIntentsItem);
		
		databaseManagementMenu = new JMenu("Database Management");
		configureDatabaseItem = new JMenuItem("Configure the Database Parameters...");
		configureDatabaseItem.addActionListener(this);
		databaseManagementMenu.add(configureDatabaseItem);
		deleteDatabaseItem = new JMenuItem("Delete a Database...");
		deleteDatabaseItem.addActionListener(this);
		databaseManagementMenu.add(deleteDatabaseItem);
		sqlUpdateItem = new JMenuItem("Execute an SQL Update Query...");
		sqlUpdateItem.addActionListener(this);
		databaseManagementMenu.add(sqlUpdateItem);
		
		databaseMenu.add(contextsMenu);
		databaseMenu.add(rulesBasisMenu);
		databaseMenu.add(latticesMenu);
		databaseMenu.add(databaseManagementMenu);
		
	}
	
	
	/* (non-Javadoc)
	 * @see lattice.gui.controller.AbstractController#getMainMenu()
	 */
	public JMenu getMainMenu() {
		return databaseMenu;
	}
	
	
	/* (non-Javadoc)
	 * @see lattice.gui.controller.AbstractController#checkPossibleActions()
	 */
	public void checkPossibleActions() {
		
		if (rce.getFamilyContexts().size() == 0) {
			saveFamilyItem.setEnabled(false);
			latticesMenu.setEnabled(false);
			saveAssociatedLatticeItem.setEnabled(false);
			exportAssociatedLatticeToXMLItem.setEnabled(false);
			viewAssociatedLatticeItem.setEnabled(false);
			viewIntentsItem.setEnabled(false);
		} else {
			saveFamilyItem.setEnabled(true);
			RelationBuilder absRel = rce.getSelectedRelation();
			
			if (absRel instanceof InterObjectBinaryRelation) {
				latticesMenu.setEnabled(false);
				saveAssociatedLatticeItem.setEnabled(false);
				exportAssociatedLatticeToXMLItem.setEnabled(false);
				viewAssociatedLatticeItem.setEnabled(false);
				viewIntentsItem.setEnabled(false);
			}
			else if (absRel instanceof ScalingBinaryRelation) {
				latticesMenu.setEnabled(false);
				saveAssociatedLatticeItem.setEnabled(false);
				exportAssociatedLatticeToXMLItem.setEnabled(false);
				viewAssociatedLatticeItem.setEnabled(false);
				viewIntentsItem.setEnabled(false);
			}
			else if (absRel instanceof MatrixBinaryRelationBuilder) {
				latticesMenu.setEnabled(true);
				exportAssociatedLatticeToXMLItem.setEnabled(true);
				viewAssociatedLatticeItem.setEnabled(true);
				if (absRel.getLattice() == null) {
					saveAssociatedLatticeItem.setEnabled(false);
					viewIntentsItem.setEnabled(false);
				} else {
					saveAssociatedLatticeItem.setEnabled(true);
					viewIntentsItem.setEnabled(true);
				}
			}
		}
	}
	
	
	/* (non-Javadoc)
	 * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
	 */
	public void actionPerformed(ActionEvent arg0) {
		
		// Relational Context Family
		
		if (arg0.getSource() == saveFamilyItem) {
			addMessage("Saving contexts to database...");
			dbm = new DatabaseManagement();
			if (DatabaseConnection.getAlwaysUseParameters()) {
				new SaveContextsDialog(dbm, rce);
			} else {
				new DatabaseConfiguration(dbm, rce, DatabaseConfiguration.SAVE_CONTEXTS_MODE);
			}
		}
		
		else if (arg0.getSource() == loadFamilyItem) {
			RelationalContextFamily relCtxFam = rce.getFamilyContexts();
			addMessage("Loading contexts from database...");
			if (DatabaseFunctions.showConfirmDialog("Do you want to clear the editor first?")) {
				while (relCtxFam.size() != 0) {
					rce.removeRelation();
				}
			} 
			dbm = new DatabaseManagement();
			if (DatabaseConnection.getAlwaysUseParameters()) {
				new LoadContextsDialog(dbm, rce);
			} else {
				new DatabaseConfiguration(dbm, rce, DatabaseConfiguration.LOAD_CONTEXTS_MODE);
			}
		}
		
		else if (arg0.getSource() == deleteContextsItem) {
			addMessage("Deleting contexts from database...");
			dbm = new DatabaseManagement();
			if (DatabaseConnection.getAlwaysUseParameters()) {
				new DeleteContextsDialog(dbm);
			} else {
				new DatabaseConfiguration(dbm, DatabaseConfiguration.DELETE_CONTEXTS_MODE);
			}
		}
		
		// Rules Basis
		
		else if (arg0.getSource() == viewAssociatedRulesBasisItem) {
			dbm = new DatabaseManagement();
			if (DatabaseConnection.getAlwaysUseParameters()) {
				DatabaseFunctions.viewRulesBasis(dbm, rce);
			} else {
				new DatabaseConfiguration(dbm, rce, DatabaseConfiguration.VIEW_RULES_BASIS_MODE);
			}
		}
		
		else if (arg0.getSource() == deleteRulesBasisItem) {
			dbm = new DatabaseManagement();
			if (DatabaseConnection.getAlwaysUseParameters()) {
				new DeleteRulesBasisDialog(dbm);
			} else {
				new DatabaseConfiguration(dbm, DatabaseConfiguration.DELETE_RULES_BASIS_MODE);
			}
		}

		else if (arg0.getSource() == exportAssociatedRulesBasisToXMLItem) {
			dbm = new DatabaseManagement();
			if (DatabaseConnection.getAlwaysUseParameters()) {
				DatabaseFunctions.exportRulesBasisToXML(dbm, rce);
			} else {
				new DatabaseConfiguration(dbm, rce, DatabaseConfiguration.EXPORT_RULES_BASIS_MODE);
			}
		}

		// Lattices

		else if (arg0.getSource() == saveAssociatedLatticeItem) {
			dbm = new DatabaseManagement();
			if (DatabaseConnection.getAlwaysUseParameters()) {
				DatabaseFunctions.saveLattice(dbm, rce);
			} else {
				new DatabaseConfiguration(dbm, rce, DatabaseConfiguration.SAVE_LATTICE_MODE);
			}
		}
		
		else if (arg0.getSource() == viewAssociatedLatticeItem) {
			dbm = new DatabaseManagement();
			if (DatabaseConnection.getAlwaysUseParameters()) {
				DatabaseFunctions.viewLattice(dbm, rce);
			} else {
				new DatabaseConfiguration(dbm, rce, DatabaseConfiguration.VIEW_LATTICE_MODE);
			}
		}
		
		else if (arg0.getSource() == deleteLatticesItem) {
			dbm = new DatabaseManagement();
			if (DatabaseConnection.getAlwaysUseParameters()) {
				new DeleteLatticesDialog(dbm);
			} else {
				new DatabaseConfiguration(dbm, DatabaseConfiguration.DELETE_LATTICES_MODE);
			}
		}
		
		else if (arg0.getSource() == exportAssociatedLatticeToXMLItem) {
			dbm = new DatabaseManagement();
			if (DatabaseConnection.getAlwaysUseParameters()) {
				DatabaseFunctions.exportLatticeToXML(dbm, rce);
			} else {
				new DatabaseConfiguration(dbm, rce, DatabaseConfiguration.EXPORT_LATTICE_MODE);
			}
		}
		
		else if (arg0.getSource() == viewIntentsItem) {
			new IntentsTableVisualization(new IntentsBasis(rce.getSelectedRelation().getLattice()), rce);
		}
		
		// Database Management
		
		else if (arg0.getSource() == configureDatabaseItem) {
			new DatabaseConfiguration(DatabaseConfiguration.CONFIG_MODE);
		}

		else if (arg0.getSource() == deleteDatabaseItem) {
			dbm = new DatabaseManagement();
			String dbName = DatabaseFunctions.showInputDialog("Enter the name of the database you want to delete:");
			if (dbName != null) {
				DatabaseFunctions.deleteDatabase(dbm, dbName);
			}
		}
		
		else if (arg0.getSource() == sqlUpdateItem) {
			dbm = new DatabaseManagement();
			if (DatabaseConnection.getAlwaysUseParameters()) {
				DatabaseFunctions.sqlUpdate(dbm,
					DatabaseFunctions.showInputDialog("Enter your SQL Update Query:"));
			}
			else {
				new DatabaseConfiguration(dbm, DatabaseConfiguration.SQL_UPDATE_MODE);
			}
		}
	}

	
	public void closeConnection() {
		if (dbm != null) dbm.closeConnection();
	}
}
