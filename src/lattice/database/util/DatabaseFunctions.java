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
 * Created on 2004-06-14
 * @author Manuel Aupetit
 */
package lattice.database.util;

import java.util.StringTokenizer;
import java.util.Vector;

import javax.swing.JOptionPane;

import lattice.database.io.DatabaseContextsReader;
import lattice.database.io.DatabaseContextsWriter;
import lattice.database.io.DatabaseLatticeReader;
import lattice.database.io.DatabaseLatticeWriter;
import lattice.database.io.DatabaseRulesBasisReader;
import lattice.database.io.DatabaseRulesBasisWriter;
import lattice.database.task.DatabaseReadingTask;
import lattice.database.task.DatabaseWritingTask;
import lattice.gui.RelationalContextEditor;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.relation.ScalingBinaryRelation;
import rule.util.RulesBasis;

/**
 * This class provides static methods to access the database.<br>
 * The majority of these methods use a <code>DatabaseManagement</code> object as parameter,<br>
 * and call specific task instances, which directly access the database using the <code>DatabaseManagement</code> instance.<br>
 * There are also tools which perform any useful task for the database.<br>
 * @author Manuel Aupetit
 */
public class DatabaseFunctions {

	// Relations Types
	public static final String UNRECOGNIZED_TYPE = "Unrecognized";
	public static final String BINARY_TYPE = "Binary";
	public static final String INTER_OBJECT_TYPE = "InterObjectBinary";
	public static final String MULTI_VALUED_TYPE = "MultiValued";
	public static final String SCALING_BINARY_TYPE = "ScalingBinary";
	
	/**
	 * A method to save a new RCF to the database
	 */
	public static void saveFamily(	DatabaseManagement dbm, Vector relations,
									String dbName, RelationalContextEditor relCtxEd) {

		//dbName = filter(dbName);
		dbm.dropDatabase(dbName);
		dbm.createDatabase(dbName);
		dbm.useDatabase(dbName);
		DatabaseConnection.setDatabase(dbName);

		DatabaseWritingTask writeTask = new DatabaseWritingTask(relCtxEd);
		writeTask.setBinRelOnUse(relations);
		writeTask.setDataWriter(new DatabaseContextsWriter(dbm, relations, relCtxEd.getFamilyContexts(), true));
		writeTask.exec();
	}


	/**
	 * A method to add relations to an existing RCF in the database
	 */
	public static void addFamily(	DatabaseManagement dbm, Vector relations,
									String dbName, RelationalContextEditor relCtxEd) {

		//dbName = filter(dbName);
		dbm.useDatabase(dbName);
		DatabaseConnection.setDatabase(dbName);

		DatabaseWritingTask writeTask = new DatabaseWritingTask(relCtxEd);
		writeTask.setBinRelOnUse(relations);
		writeTask.setDataWriter(new DatabaseContextsWriter(dbm, relations, relCtxEd.getFamilyContexts(), false));
		writeTask.exec();

	}


	/**
	 * A method to load a RCF from the database
	 */
	public static void loadFamily(	DatabaseManagement dbm, RelationalContextEditor relCtxEd,
									Vector relations, String relCtxName) {

		relCtxEd.setTitle("Contexts Family name: " + relCtxName);
		DatabaseReadingTask readingTask = new DatabaseReadingTask(relCtxEd);
		readingTask.setDataReader(new DatabaseContextsReader(dbm, relations, relCtxName));
		readingTask.exec();
	}
	
	
	/**
	 * A method to delete contexts from the database
	 */
	public static void deleteContexts(DatabaseManagement dbm, Vector relations, String dbName) {
		 
		//dbName = filter(dbName);
		dbm.useDatabase(dbName);
		DatabaseConnection.setDatabase(dbName);
		dbm.deleteRelations(relations);
	}
	

	/**
	 * A method to delete contexts from the database
	 */
	public static void deleteContexts(DatabaseManagement dbm, Vector relations) {
		deleteContexts(dbm, relations, (DatabaseConnection.getDatabase()));
	}
	
	
	/**
	 * A method to delete an entire database (i.e. a complete RCF)
	 */
	public static void deleteDatabase(DatabaseManagement dbm, String dbName) {
		dbm.dropDatabase(dbName);
	}
	
	
	/**
	 * A method to perform direct SQL updates in the database (for expert users only)
	 */
	public static void sqlUpdate(DatabaseManagement dbm, String query) {
		if (query != null && !query.equals("")) {
			dbm.sqlUpdate(query);
		}
	}
	
	/**
	 * A method to get the type of the relation in parameter (does not use the database)<br>
	 * The type can be Binary, InterObjectBinary, MultiValued, ScalingBinary, or Unrecognized
	 */
	public static String getRelationType(RelationBuilder absRel) {
		if (absRel instanceof InterObjectBinaryRelation) return INTER_OBJECT_TYPE;
		if (absRel instanceof ScalingBinaryRelation) return SCALING_BINARY_TYPE;
		if (absRel instanceof MatrixBinaryRelationBuilder) return BINARY_TYPE;
		return UNRECOGNIZED_TYPE;
	}
	
	
	/**
	 * A method to get the relations related to the relation in parameter (does not use the database)
	 */
	public static Vector getRelatedRelations(RelationalContextFamily relCtxFam, RelationBuilder absRel) {

		Vector result = new Vector();
		if (getRelationType(absRel).equals(INTER_OBJECT_TYPE)) {
			String obj = ((InterObjectBinaryRelation)absRel).getObjectsContextName();
			String att = ((InterObjectBinaryRelation)absRel).getAttributesContextName();
			result.addElement(relCtxFam.getForName(obj));
			if (!obj.equals(att)) {
				result.addElement(relCtxFam.getForName(att));
			}
		}
		
		return result;
	}
	
	
	/**
	 * A method to check the existence of the relation in the database 
	 * @return boolean true if the relation is found, else false
	 */
	public static boolean isRelationExisting(DatabaseManagement dbm, String relName) {
		return dbm.isRelationExisting(relName);
	}
	
	
	/*********************************************************************/
	/**								RULES BASIS							**/
	/*********************************************************************/
	
	/**
	 * A method to save a rules basis in the database 
	 */
	public static void saveRulesBasis(DatabaseManagement dbm, RulesBasis rulesBasis, RelationalContextEditor relCtxEd) {
		
		Vector relation = new Vector(1);
		relation.addElement(rulesBasis.getAbstractRelation());
		DatabaseWritingTask writeTask = new DatabaseWritingTask(relCtxEd);
		writeTask.setBinRelOnUse(relation);
		writeTask.setDataWriter(new DatabaseRulesBasisWriter(dbm, rulesBasis));
		writeTask.exec();
	}

	/**
     * A method to get the rules basis from the database and launch the visualization through a specific task
     */
    public static void viewRulesBasis(DatabaseManagement dbm, RelationalContextEditor relCtxEd) {
		try {
			RelationBuilder absRel = relCtxEd.getSelectedRelation();
			Vector rulesBasisVect = getRelationRulesBasisList(dbm, (absRel.getName()));
			
			if (rulesBasisVect != null && rulesBasisVect.size() != 0) {
				String rulesBasisID = getRulesBasisIDFromList(rulesBasisVect);
				if (rulesBasisID != null) {
					Vector relOnUse = new Vector(1);
					relOnUse.addElement(absRel);
					DatabaseReadingTask readingTask = new DatabaseReadingTask(relCtxEd);
					readingTask.setBinRelOnUse(relOnUse);
					readingTask.setDataReader(new DatabaseRulesBasisReader(dbm, rulesBasisID, absRel, "View Rules Basis"));
					readingTask.exec();
				}
			} else {
				showMessageDialog("There are no rules basis associated to this relation");
			}
		} catch (Exception e) {
			System.err.println("Empty Family");
			e.printStackTrace();
		}
    }
    
	
	/**
	 * A method to delete rules basis from the current database
	 */
	public static void deleteRulesBasis(DatabaseManagement dbm, Vector rulesBasisIDs) {
		deleteRulesBasis(dbm, rulesBasisIDs, DatabaseConnection.getDatabase());
	}

	/**
	 * A method to delete rules basis from the database
	 */
	public static void deleteRulesBasis(DatabaseManagement dbm, Vector rulesBasisIDs, String dbName) {
		dbName = (dbName);
		dbm.useDatabase(dbName);
		DatabaseConnection.setDatabase(dbName);
		dbm.deleteRulesBasis(rulesBasisIDs);
	}
	
	
	/**
	 * A method to perform the XML exportation of the rules basis from the database<br>
	 * (the rules basis to export are asked to the user through a GUI)
	 */
	public static void exportRulesBasisToXML(DatabaseManagement dbm, RelationalContextEditor relCtxEd) {

		try {
			RelationBuilder absRel = relCtxEd.getSelectedRelation();
			Vector rulesBasisVect = getRelationRulesBasisList(dbm, (absRel.getName()));

			if (rulesBasisVect != null && rulesBasisVect.size() != 0) {
				String rulesBasisID = getRulesBasisIDFromList(rulesBasisVect);
				if (rulesBasisID != null) {
					Vector relOnUse = new Vector(1);
					relOnUse.addElement(absRel);
					DatabaseReadingTask readingTask = new DatabaseReadingTask(relCtxEd);
					readingTask.setBinRelOnUse(relOnUse);
					readingTask.setDataReader(new DatabaseRulesBasisReader(dbm, rulesBasisID, absRel, "Export Rules Basis"));
					readingTask.exec();
				}
			} else {
				showMessageDialog("There are no rules basis associated to this relation");
			}
		} catch (Exception e) {
			System.err.println("Error exporting the rules basis");
		}
	}
	
	/**
	 * A method to get a <code>RulesBasis</code> object from the database with the specified rules basis ID
	 */
	public static RulesBasis getRulesBasis(DatabaseManagement dbm, String rulesBasisID, RelationBuilder absRel) {
		return new RulesBasis(absRel, dbm.getDatasetName(rulesBasisID), dbm.getRules(rulesBasisID), dbm.getMinSupport(rulesBasisID), dbm.getMinConfidence(rulesBasisID));
	}
	
	
	/**
	 * A method to get the selected rules basis ID from a list (use a popup dialog)<br>
	 * Does not use the database
	 */
	public static String getRulesBasisIDFromList(Vector rulesBasisList) {
		String[] rulesBasis = new String[rulesBasisList.size()];
		for (int i=0; i<rulesBasisList.size(); i++) {
			rulesBasis[i] = rulesBasisList.get(i).toString();
		}
		String rulesBasisResult = showInputDialog("Select the rules basis:", rulesBasis);
		return getRulesBasisIDFromDescription(rulesBasisResult);
	}

	
	/**
	 * A method to get the rules basis ID from its string description<br>
	 * Does not use the database
	 */
	public static String getRulesBasisIDFromDescription(String rulesBasisDesc) {
		if (rulesBasisDesc != null) {
			String rulesBasisID = rulesBasisDesc.substring(4, rulesBasisDesc.length());
			return (new StringTokenizer(rulesBasisID)).nextToken("[");
		}
		return null;
	}

	
	/**
	 * A method to get the list of all rules basis in the database
	 */
	public static Vector getAllRulesBasisList(DatabaseManagement dbm) {
		return dbm.getAllRulesBasisList();
	}
	
	/**
	 * A method to get the list of the rules basis in the database related to the specified relation
	 */
	public static Vector getRelationRulesBasisList(DatabaseManagement dbm, String relName) {
		return dbm.getRelationRulesBasisList(relName);
	}
	
	
	/*********************************************************************/
	/**								LATTICES							**/
	/*********************************************************************/


	/**
	 * A method to save a lattice to the current database 
	 */
	public static void saveLattice(DatabaseManagement dbm, RelationalContextEditor relCtxEd) {
		saveLattice(dbm, relCtxEd, DatabaseConnection.getDatabase());
	}
	
	
	/**
	 * A method to save a lattice to the specified database
	 */
	public static void saveLattice(DatabaseManagement dbm, RelationalContextEditor relCtxEd, String dbName) {
		dbName = (dbName);
		dbm.useDatabase(dbName);
		DatabaseConnection.setDatabase(dbName);

		RelationBuilder absRel = relCtxEd.getSelectedRelation();
		if (absRel.getLattice() != null) { 
			if (isRelationExisting(dbm, (absRel.getName()))) {
				Vector relOnUse = new Vector(1);
				relOnUse.addElement(absRel);
				DatabaseWritingTask writeTask = new DatabaseWritingTask(relCtxEd);
				writeTask.setBinRelOnUse(relOnUse);
				writeTask.setDataWriter(new DatabaseLatticeWriter(dbm, absRel));
				writeTask.exec();
			} else {
				showMessageDialog("Save the relation '" + absRel.getName() + "' in the database first");
			}
		} else {
			showMessageDialog("This context has no associated lattice graph");
		}
	}
	
	
	/**
	 * A method to view a lattice, selected from the database with a GUI
	 */
	public static void viewLattice(DatabaseManagement dbm, RelationalContextEditor relCtxEd) { 
		try {
			Vector latticesVect = getRelationLatticesList(dbm, (relCtxEd.getSelectedRelation().getName()));
			if (latticesVect != null && latticesVect.size() != 0) {

				String latticeID = getLatticeIDFromList(latticesVect);
				if (latticeID != null) {
					Vector relOnUse = new Vector(1);
					relOnUse.addElement(relCtxEd.getSelectedRelation());
					DatabaseReadingTask readingTask = new DatabaseReadingTask(relCtxEd);
					readingTask.setBinRelOnUse(relOnUse);
					readingTask.setDataReader(new DatabaseLatticeReader(dbm, latticeID, "View Lattice"));
					readingTask.exec();
				}
			} else {
				showMessageDialog("There are no lattices associated to this relation");
			}
		} catch (Exception e) {
			System.err.println("Error viewing the lattice");
		}
	}
	
	
	/**
	 * A method to perform the XML exportation of a lattice from the database, selected through a GUI
	 */
	public static void exportLatticeToXML(DatabaseManagement dbm, RelationalContextEditor relCtxEd) {
		try {
			Vector latticesVect = getRelationLatticesList(dbm, (relCtxEd.getSelectedRelation().getName()));
			if (latticesVect != null && latticesVect.size() != 0) {

				String latticeID = getLatticeIDFromList(latticesVect);
				if (latticeID != null) {
					Vector relOnUse = new Vector(1);
					relOnUse.addElement(relCtxEd.getSelectedRelation());
					DatabaseReadingTask readingTask = new DatabaseReadingTask(relCtxEd);
					readingTask.setBinRelOnUse(relOnUse);
					readingTask.setDataReader(new DatabaseLatticeReader(dbm, latticeID, "Export Lattice"));
					readingTask.exec();
				}
			} else {
				showMessageDialog("There are no lattices associated to this relation");
			}
		} catch (Exception e) {
			System.err.println("Error exporting the lattice");
		}
	}
	
	
	/**
	 * A method to get the list of the lattices from the database related to the specified relation
	 */
	public static Vector getRelationLatticesList(DatabaseManagement dbm, String relName) {
		return dbm.getRelationLatticesList(relName);
	}
	
	
	/**
	 * A method to get the list of all lattices stored in the database
	 */
	public static Vector getAllLatticesList(DatabaseManagement dbm) {
		return dbm.getAllLatticesList();
	}
	
	
	/**
	 * A method to get the lattice ID from a list (the lattice is selected through a GUI)<br>
	 * Does not use the database 
	 */
	public static String getLatticeIDFromList(Vector latticesList) {
		String[] lattices = new String[latticesList.size()];
		for (int i=0; i<latticesList.size(); i++) {
			lattices[i] = latticesList.get(i).toString();
		}
		String latticeResult = showInputDialog("Select the lattice you want to export:", lattices);
		return getLatticeIDFromDescription(latticeResult);
	}
	
	
	/**
	 * A method to get the lattice ID from its string description<br>
	 * Does not use the database
	 */
	public static String getLatticeIDFromDescription(String latticeDesc) {
		if (latticeDesc != null) {
			String latticeID = latticeDesc.substring(4, latticeDesc.length());
			return (new StringTokenizer(latticeID)).nextToken("[");
		}
		return null;
	}
	
	
	/**
	 * A method to delete the selected lattices from the database
	 */
	public static void deleteLattices(DatabaseManagement dbm, Vector lattices) {
		dbm.deleteLattices(lattices);
	}
	
	
	/*********************************************************************/
	/**								UTILS								**/
	/*********************************************************************/
	
	
	/**
	 * A method to roughly filter the names in order to use them in a MySQL database<br>
	 * Has to be improved...
	 */
	public static String filter(String str) {
		char[] ch = str.toCharArray();
        char[] badChars = "_".toCharArray();

		for (int i=0; i<ch.length; i++) {
			for (int j=0; j<badChars.length; j++) {
				if ( ch[i] == badChars[j] ) {
					ch[i] = '_';
				}
			}
		}
		return new String(ch);
	}
	
	
	public static boolean showConfirmDialog(String message) {
		return JOptionPane.showConfirmDialog(
					null, message, "Confirmation required", JOptionPane.YES_NO_OPTION)
				== JOptionPane.YES_OPTION;
	}
	
	
	public static boolean showWarningDialog(String message) {
		return JOptionPane.showConfirmDialog(
					null, message, "Warning", JOptionPane.OK_CANCEL_OPTION,
					JOptionPane.WARNING_MESSAGE) == JOptionPane.OK_OPTION;
	}
	

	public static String showInputDialog(String message) {
		return JOptionPane.showInputDialog(
			null, message, "Input required", JOptionPane.QUESTION_MESSAGE);
	}
	

	public static String showInputDialog(String message, String defaultValue) {
		return (String) JOptionPane.showInputDialog(null, message, "Input required", JOptionPane.QUESTION_MESSAGE, null, null, defaultValue);
	}
	
	
	public static void showMessageDialog(String message) {
		JOptionPane.showMessageDialog(null, message);
	}
	
	
	public static String showInputDialog(String message, Object[] values) {

		if (values != null || values.length > 0) {

			return (String) JOptionPane.showInputDialog(
						null, message, "Choice required",
						JOptionPane.INFORMATION_MESSAGE, null,
						values, values[0]);
		}
		return null;
	}
	
}
