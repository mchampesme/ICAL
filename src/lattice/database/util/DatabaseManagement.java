/*
 * **********************************************************************
 * Copyright (C) 2004 The Galicia Team Modifications to the initial code base
 * are copyright of their respective authors, or their employers as appropriate.
 * Authorship of the modifications may be determined from the ChangeLog placed
 * at the end of this file. This program is free software; you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of the
 * License, or (at your option) any later version. This program is distributed
 * in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even
 * the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details. You should have
 * received a copy of the GNU Lesser General Public License along with this
 * program; if not, write to the Free Software Foundation, Inc., 59 Temple
 * Place, Suite 330, Boston, MA 02111-1307 USA; or visit the following url:
 * http://www.gnu.org/copyleft/lesser.html
 * **********************************************************************
 */

/*
 * Created on 2004-06-23
 * @author Manuel Aupetit
 */
package lattice.database.util;

import java.sql.ResultSet;
import java.sql.Statement;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.Vector;

import lattice.alpha.util.BGIntent;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.DefaultFormalObject;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.relation.ScalingBinaryRelation;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.CompleteConceptLatticeImp;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
import lattice.util.structure.LatticeGraph;
import rule.util.Rule;

/**
 * A class that contains methods to manage directly the database
 * 
 * @author Manuel Aupetit
 */
public class DatabaseManagement {

    private DatabaseConnection dbc = null;

    private Statement stat = null;

    private ResultSet rs = null;

    public static final String RELATION_NAME = "Relation_Name";

    // RCF Database Schema
    public static final String RCF_RELATIONS_PROPERTIES = "RCF_Relations_Properties";

    public static final String RCF_RELATIONS_DEPENDENCES = "RCF_Relations_Dependences";

    public static final String TABLE_TYPE = "Table_Type";

    public static final String OBJECTS_TABLE = "Objects_Table";

    public static final String ATTRIBUTES_TABLE = "Attributes_Table";

    public static final String PARENT_RELATION = "Parent_Relation";

    public static final String OBJ_TABLE_SUFFIX = "_Obj";

    public static final String ATT_TABLE_SUFFIX = "_Att";

    public static final String OBJ_COLUMN = "Object";

    public static final String ATT_COLUMN = "Attribute";

    public static final String VAL_COLUMN = "Value";

    public static final String IOR_OBJ_COLUMN = "Object1";

    public static final String IOR_ATT_COLUMN = "Object2";

    // RCF Rules Schema
    public static final String RCF_RULES_BASIS_PROPERTIES = "RCF_Rules_Basis_Properties";

    public static final String RULES_BASIS_ID = "ID";

    public static final String DATASET_NAME = "Dataset_Name";

    public static final String MIN_SUPPORT = "Min_Support";

    public static final String MIN_CONFIDENCE = "Min_Confidence";

    public static final String RCF_RULES_BASIS = "RCF_Rules_Basis";

    public static final String PREMISE = "Premise";

    public static final String CONSEQUENCE = "Consequence";

    public static final String SUPPORT = "Support";

    public static final String CONFIDENCE = "Confidence";

    public static final String SEPARATOR = "|";

    // public static final String RULES_SUFFIX = "_Rules";

    // RCF Lattices Schema
    public static final String RCF_LATTICES_PROPERTIES = "RCF_Lattices_Properties";

    public static final String LATTICE_ID = "ID";

    public static final String LATTICE_DESCRIPTION = "Description";

    public static final String LATTICE_TYPE = "Type";

    public static final String LATTICE_TOP_NODE = "Top_Node";

    public static final String LATTICE_BOTTOM_NODE = "Bottom_Node";

    public static final String RCF_LATTICES_NODES = "RCF_Lattices_Nodes";

    public static final String RCF_LATTICES_PARENTS = "RCF_Lattices_Parents";

    public static final String LATTICE_NODE = "Lattice_Node";

    public static final String PARENT_NODE = "Parent_Node";

    public static final String RCF_LATTICES_EXTENTS = "RCF_Lattices_Extents";

    public static final String LATTICE_OBJECT = "Object";

    public static final String RCF_LATTICES_INTENTS = "RCF_Lattices_Intents";

    public static final String LATTICE_ATTRIBUTE = "Attribute";

    public static final String RCF_LATTICES_GENERATORS = "RCF_Lattices_Generators";

    public static final String LATTICE_GENERATOR = "Generator";

    /**
     * The default constructor
     */
    public DatabaseManagement() {
        this(new DatabaseConnection());
    }

    /**
     * The constructor using an existing DatabaseConnection
     */
    public DatabaseManagement(DatabaseConnection dbc) {
        this.dbc = dbc;
    }

    /**
     * Gets the current DatabaseConnection attribute
     */
    public DatabaseConnection getConnection() {
        return this.dbc;
    }

    /**
     * A method that drops the database in the current running server, using a
     * database name in parameter
     */
    public void dropDatabase(String dbName) {

        try {
            stat = dbc.getConnection().createStatement();
            stat.executeUpdate("DROP DATABASE IF EXISTS " + dbName);

        } catch (Exception e) {
            System.err.println("The Database '" + dbName
                               + "' cannot be dropped");
        }
    }

    /**
     * A method that creates the database in the current running server, using a
     * database name in parameter
     */
    public void createDatabase(String dbName) {

        try {
            stat = dbc.getConnection().createStatement();
            stat.executeUpdate("CREATE DATABASE IF NOT EXISTS " + dbName);

        } catch (Exception e) {
            System.err.println("The Database '" + dbName
                               + "' cannot be created");
        }
    }

    /**
     * A method that selects the database in parameter
     */
    public void useDatabase(String dbName) {

        try {
            stat = dbc.getConnection().createStatement();
            stat.executeUpdate("USE " + dbName);

        } catch (Exception e) {
            System.err.println("The Database cannot be changed to '" + dbName
                               + "'");
        }
    }

    /*********************************************************************/
    /** CONTEXTS **/
    /*********************************************************************/

    /**
     * A method to delete a list of relations from the database
     */
    public void deleteRelations(Vector relations) {

        for (int i = 0; i < relations.size(); i++) {
            deleteRelation(DatabaseFunctions
                    .filter(relations.get(i).toString()));
        }
    }

    /**
     * A method to delete a single relation from the database
     */
    public void deleteRelation(String relName) {

        // Deletes the rules basis & lattices related to this relation
        deleteRulesBasis(getRulesBasisIDsOfRelation(relName));
        deleteLattices(getRelationLatticesList(relName));

        String deleteSchema = "DELETE FROM " + RCF_RELATIONS_PROPERTIES
                              + " WHERE " + RELATION_NAME + " = '";

        String deleteDerived = "DELETE FROM " + RCF_RELATIONS_DEPENDENCES
                               + " WHERE " + PARENT_RELATION + " = '" + relName
                               + "'";

        String deleteParent = "DELETE FROM " + RCF_RELATIONS_DEPENDENCES
                              + " WHERE " + RELATION_NAME + " = '" + relName
                              + "'";

        String dropTableGeneric = "DROP TABLE IF EXISTS ";

        String relType = getRelationType(relName);

        if (!relType.equals(DatabaseFunctions.UNRECOGNIZED_TYPE)) {

            try {

                stat = dbc.getConnection().createStatement();

                // Deletes the derived contexts and entries
                Vector derived = getDerivedContexts(relName);
                for (int i = 0; i < derived.size(); i++) {
                    String derivedName = derived.get(i).toString();
                    String derivedType = getRelationType(derivedName);
                    if (derivedType
                            .equals(DatabaseFunctions.SCALING_BINARY_TYPE)) {
                        if (DatabaseFunctions
                                .showConfirmDialog("Also deletes the '"
                                                   + derivedName
                                                   + "' scaling relation derived from '"
                                                   + relName + "'?")) {
                            stat.executeUpdate(deleteDerived);
                            deleteRelation(derivedName);
                        }
                    } else if (!derivedType
                            .equals(DatabaseFunctions.UNRECOGNIZED_TYPE)) {
                        stat.executeUpdate(deleteDerived);
                        deleteRelation(derivedName);
                    }
                }

                // Deletes the main table
                stat.executeUpdate(dropTableGeneric + relName);

                // Deletes the parent contexts of the current one (if confirmed)
                Vector parents = getParentContexts(relName);
                stat.executeUpdate(deleteParent);
                if (!parents.isEmpty()) {
                    if (DatabaseFunctions
                            .showConfirmDialog("Also delete the contexts from which '"
                                               + relName + "' derives?")) {
                        for (int i = 0; i < parents.size(); i++) {
                            deleteRelation(parents.get(i).toString());
                        }
                    }
                }

                // Deletes the entry in the schema
                stat.executeUpdate(deleteSchema + relName + "'");

                if (!relType.equals(DatabaseFunctions.INTER_OBJECT_TYPE)) {
                    // Deletes the Objects and Attributes tables
                    stat.executeUpdate(dropTableGeneric + relName
                                       + OBJ_TABLE_SUFFIX);
                    stat.executeUpdate(dropTableGeneric + relName
                                       + ATT_TABLE_SUFFIX);
                }

            } catch (Exception e) {
                System.err
                        .println("Error deleting relations from the RCF Schema");
            }
        }
    }

    /**
     * A method to create a RCF Schema (creates the tables and then adds the
     * relations)
     */
    public void createRCFSchema(Vector relations,
                                RelationalContextFamily relCtxFam) {

        String dropSchema = "DROP TABLE IF EXISTS " + RCF_RELATIONS_PROPERTIES;
        String createSchema = "CREATE TABLE " + RCF_RELATIONS_PROPERTIES + " ("
                              + RELATION_NAME + " VARCHAR(30) PRIMARY KEY, "
                              + TABLE_TYPE + " VARCHAR(30) NOT NULL, "
                              + OBJECTS_TABLE + " VARCHAR(30) NOT NULL, "
                              + ATTRIBUTES_TABLE + " VARCHAR(30) NOT NULL)";

        String dropDerivationsTable = "DROP TABLE IF EXISTS "
                                      + RCF_RELATIONS_DEPENDENCES;
        String createDerivationsTable = "CREATE TABLE "
                                        + RCF_RELATIONS_DEPENDENCES + " ("
                                        + RELATION_NAME
                                        + " VARCHAR(30) NOT NULL REFERENCES "
                                        + RCF_RELATIONS_PROPERTIES
                                        + " ON DELETE CASCADE, "
                                        + PARENT_RELATION
                                        + " VARCHAR(30) NOT NULL REFERENCES "
                                        + RCF_RELATIONS_PROPERTIES
                                        + " ON DELETE CASCADE, PRIMARY KEY ("
                                        + RELATION_NAME + ", "
                                        + PARENT_RELATION + "))";

        try {
            stat = dbc.getConnection().createStatement();
            stat.executeUpdate(dropSchema);
            stat.executeUpdate(createSchema);
            stat.executeUpdate(dropDerivationsTable);
            stat.executeUpdate(createDerivationsTable);

        } catch (Exception e) {
            System.err.println("Error creating the RCF Schema Tables");
        }

        createRCFRulesBasisSchema();
        createRCFLatticesSchema();
        addRelationsToRCFSchema(relations, relCtxFam);

    }

    /**
     * A method to add relations to a previously created RCF Schema
     */
    public void addRelationsToRCFSchema(Vector relations,
                                        RelationalContextFamily relCtxFam) {

        String insertGeneric = "INSERT INTO " + RCF_RELATIONS_PROPERTIES
                               + " VALUES (";

        try {
            stat = dbc.getConnection().createStatement();

            for (int i = 0; i < relations.size(); i++) {

                RelationBuilder absRel = (RelationBuilder) relations.get(i);
                String relName = DatabaseFunctions.filter(absRel.getName());
                String insert = insertGeneric + "'" + relName + "', ";

                if (absRel instanceof ScalingBinaryRelation) {

                    insert += "'" + DatabaseFunctions.SCALING_BINARY_TYPE
                              + "', '" + relName + OBJ_TABLE_SUFFIX + "', '"
                              + relName + ATT_TABLE_SUFFIX + "')";
                    stat.executeUpdate(insert);
                    String message = "Please choose the parent relation of '"
                                     + relName + "'";

                    addToDependencesTable(relName,
                                          DatabaseFunctions
                                                  .showInputDialog(message,
                                                                   getRelationsOfType(relCtxFam,
                                                                                      DatabaseFunctions.MULTI_VALUED_TYPE)));
                    createBinaryTable(relName, (ScalingBinaryRelation) absRel);
                } else if (absRel instanceof MatrixBinaryRelationBuilder) {
                    insert += "'" + DatabaseFunctions.BINARY_TYPE + "', '"
                              + relName + OBJ_TABLE_SUFFIX + "', '" + relName
                              + ATT_TABLE_SUFFIX + "')";
                    stat.executeUpdate(insert);
                    createBinaryTable(relName,
                                      (MatrixBinaryRelationBuilder) absRel);
                }
            }
        } catch (Exception e) {
            System.err
                    .println("Error adding relations to the RCF Schema Table");
            e.printStackTrace();
        }
    }

    /**
     * A method to create tables and fill a binary relation in the database
     */
    public void createBinaryTable(String tableName,
                                  MatrixBinaryRelationBuilder binRel) {

        String objTable = tableName + OBJ_TABLE_SUFFIX;
        String attTable = tableName + ATT_TABLE_SUFFIX;

        String createObjTable = "CREATE TABLE " + objTable + " (" + OBJ_COLUMN
                                + " VARCHAR(30) PRIMARY KEY)";
        String createAttTable = "CREATE TABLE " + attTable + " (" + ATT_COLUMN
                                + " VARCHAR(30) PRIMARY KEY)";
        String createBinaryTable = "CREATE TABLE " + tableName + " ("
                                   + OBJ_COLUMN
                                   + " VARCHAR(30) NOT NULL REFERENCES "
                                   + objTable + " ON DELETE CASCADE, "
                                   + ATT_COLUMN
                                   + " VARCHAR(30) NOT NULL REFERENCES "
                                   + attTable
                                   + " ON DELETE CASCADE, PRIMARY KEY ("
                                   + OBJ_COLUMN + ", " + ATT_COLUMN + "))";

        String insertObj = "INSERT INTO " + objTable + " VALUES ('";
        String insertAtt = "INSERT INTO " + attTable + " VALUES ('";
        String insertBinary = "INSERT INTO " + tableName + " VALUES ('";
        List<FormalObject> obj = binRel.getObjects();
        List<FormalAttribute> att = binRel.getAttributes();

        try {
            stat = dbc.getConnection().createStatement();

            stat.executeUpdate(createObjTable);
            stat.executeUpdate(createAttTable);
            stat.executeUpdate(createBinaryTable);

            for (int i = 0; i < obj.size(); i++) {
                stat.executeUpdate(insertObj
                                   + filterObjName(obj.get(i).toString())
                                   + "')");
            }

            for (int j = 0; j < att.size(); j++) {
                stat.executeUpdate(insertAtt
                                   + filterAttName(att.get(j).toString())
                                   + "')");
            }

            for (int i = 0; i < obj.size(); i++) {
                for (int j = 0; j < att.size(); j++) {
                    if (binRel.getRelation(i, j).toString().equals("X")) {

                        stat.executeUpdate(insertBinary
                                           + filterObjName(obj.get(i)
                                                   .toString())
                                           + "', '"
                                           + filterAttName(att.get(j)
                                                   .toString()) + "')");
                    }
                }
            }

        } catch (Exception e) {
            System.err.println("Error during the creation of a Binary Table");
            e.printStackTrace();
        }
    }

    /**
     * A method to add a dependance relation in the table
     */
    public void addToDependencesTable(String tableName, String parentRelation) {

        String insertDependences = "INSERT INTO " + RCF_RELATIONS_DEPENDENCES
                                   + " VALUES ('" + tableName + "', '"
                                   + parentRelation + "')";
        try {
            stat = dbc.getConnection().createStatement();
            stat.executeUpdate(insertDependences);

        } catch (Exception e) {
            System.err.println("Error adding a dependence to the RCF Schema");
        }
    }

    /**
     * A method to get the objects of the table in parameter
     */
    public Vector getObjects(String tableName) {
        Vector result = new Vector();
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT * FROM " + tableName
                                   + OBJ_TABLE_SUFFIX);
            while (rs.next()) {
                result.addElement(new DefaultFormalObject(rs.getString(1)));
            }
        } catch (Exception e) {
            System.err.println("Error getting the objects");
        }
        return result;
    }

    /**
     * A method to get the inter-object relation objects context name from its
     * table name
     */
    public String getIORObjectsContextName(String tableName) {
        String result = null;
        try {
            stat = dbc.getConnection().createStatement();
            String query = "SELECT " + OBJECTS_TABLE + " FROM "
                           + RCF_RELATIONS_PROPERTIES + " WHERE "
                           + RELATION_NAME + " = '" + tableName + "'";
            rs = stat.executeQuery(query);
            rs.next();
            result = rs.getString(1);
            result = result.substring(0,
                                      result.length()
                                              - OBJ_TABLE_SUFFIX.length());

        } catch (Exception e) {
            System.err.println("Error getting the IOR Objects Context Name");
        }
        return result;
    }

    /**
     * A method to get the inter-object relation attributes context name from
     * its table name
     */
    public String getIORAttributesContextName(String tableName) {
        String result = null;
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + ATTRIBUTES_TABLE + " FROM "
                                   + RCF_RELATIONS_PROPERTIES + " WHERE "
                                   + RELATION_NAME + " = '" + tableName + "'");
            rs.next();
            result = rs.getString(1);
            result = result.substring(0,
                                      result.length()
                                              - OBJ_TABLE_SUFFIX.length());

        } catch (Exception e) {
            System.err.println("Error getting the IOR Attributes Context Name");
        }
        return result;
    }

    /**
     * A method to get the attributes of table in parameter
     */
    public Vector getAttributes(String tableName) {

        Vector result = new Vector();
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT * FROM " + tableName
                                   + ATT_TABLE_SUFFIX);
            while (rs.next()) {
                result.addElement(new DefaultFormalAttribute(rs.getString(1)));
            }
        } catch (Exception e) {
            System.err.println("Error getting the attributes");
        }
        return result;
    }

    /**
     * A method to get the binary relation between an object and its attributes
     * 
     * @return a <code>Vector</code> that contains the attributes of an object
     */
    public Vector getBinaryRelation(String tableName, String object) {
        Vector result = new Vector();
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + ATT_COLUMN + " FROM "
                                   + tableName + " WHERE " + OBJ_COLUMN
                                   + " = '" + object + "'");
            while (rs.next()) {
                result.addElement(rs.getString(1));
            }
        } catch (Exception e) {
            System.err.println("Error getting the Binary Relation");
        }
        return result;
    }

    /**
     * A method to get the inter-object binary relation between an object and
     * its attributes
     * 
     * @return a <code>Vector</code> that contains the attributes of an object
     */
    public Vector getInterObjectBinaryRelation(String tableName, String object) {
        Vector result = new Vector();
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + IOR_ATT_COLUMN + " FROM "
                                   + tableName + " WHERE " + IOR_OBJ_COLUMN
                                   + " = '" + object + "'");
            while (rs.next()) {
                result.addElement(rs.getString(1));
            }
        } catch (Exception e) {
            System.err
                    .println("Error getting the Inter Object Binary Relation");
        }
        return result;
    }

    /**
     * A method to get the valued relation between an object and its attributes
     * 
     * @return a <code>Vector</code> that contains the values of an object for a
     *         specified attribute
     */
    public Vector getValuedRelation(String tableName, String object,
                                    String attribute) {
        Vector result = new Vector();
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + VAL_COLUMN + " FROM "
                                   + tableName + " WHERE " + OBJ_COLUMN
                                   + " = '" + object + "' AND " + ATT_COLUMN
                                   + " = '" + attribute + "'");
            while (rs.next()) {
                if (rs.getString(1) != null) {
                    result.addElement(rs.getString(1));
                }
            }
        } catch (Exception e) {
            System.err.println("Error getting the Valued Relation");
        }
        return result;
    }

    /**
     * A method to get all the tables of the current database
     */
    public Vector getTables() {

        Vector tables = new Vector();
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + RELATION_NAME + " FROM "
                                   + RCF_RELATIONS_PROPERTIES);
            while (rs.next()) {
                tables.addElement(rs.getString(1));
            }
        } catch (Exception e) {
            System.err.println("Error getting the tables list");
        }
        return tables;
    }

    /**
     * A method to get from the database the type of a relation
     */
    public String getRelationType(String tableName) {

        String query = "SELECT " + TABLE_TYPE + " FROM "
                       + RCF_RELATIONS_PROPERTIES + " WHERE " + RELATION_NAME
                       + " = '" + tableName + "'";
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery(query);
            rs.first();
            if (rs.isLast()) {
                return rs.getString(1);
            }
        } catch (Exception e) {
            System.err.println("Error getting the relation type");
        }
        return DatabaseFunctions.UNRECOGNIZED_TYPE;
    }

    /**
     * A method to get from the database the parents of a relation
     */
    public Vector getParentContexts(String relName) {
        Vector result = new Vector();
        String query = "SELECT " + PARENT_RELATION + " FROM "
                       + RCF_RELATIONS_DEPENDENCES + " WHERE " + RELATION_NAME
                       + " = '" + relName + "'";
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery(query);
            while (rs.next()) {
                result.addElement(rs.getString(1));
            }
        } catch (Exception e) {
            System.err.println("Error getting the parent contexts of '"
                               + relName + "'");
        }
        return result;
    }

    /**
     * A method to get from the database the derived contexts of a relation
     */
    public Vector getDerivedContexts(String relName) {
        Vector result = new Vector();
        String query = "SELECT " + RELATION_NAME + " FROM "
                       + RCF_RELATIONS_DEPENDENCES + " WHERE "
                       + PARENT_RELATION + " = '" + relName + "'";
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery(query);
            while (rs.next()) {
                result.addElement(rs.getString(1));
            }
        } catch (Exception e) {
            System.err.println("Error getting the contexts derived from '"
                               + relName + "'");
        }
        return result;
    }

    /**
     * A method to get all the relations of a certain type
     */
    public String[] getRelationsOfType(RelationalContextFamily relCtxFam,
                                       String type) {

        Vector tempResult = new Vector();
        for (int i = 0; i < relCtxFam.size(); i++) {
            String relName = relCtxFam.get(i).getName();
            if (getRelationType(relName).equals(type)) {
                tempResult.addElement(relName);
            }
        }

        String[] result = new String[tempResult.size()];
        for (int j = 0; j < result.length; j++) {
            result[j] = (String) tempResult.get(j);
        }
        return result;
    }

    /**
     * A method to check if a relation exists in the database
     */
    public boolean isRelationExisting(String relName) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + RELATION_NAME + " FROM "
                                   + RCF_RELATIONS_PROPERTIES + " WHERE "
                                   + RELATION_NAME + " = '" + relName + "'");
            rs.first();
            if (rs.last()) {
                return true;
            }
        } catch (Exception e) {
            System.err.println("Error getting the relation '" + relName + "'");
        }
        return false;
    }

    /*********************************************************************/
    /** RULES **/
    /*********************************************************************/

    /**
     * A method to create the Rules Basis Relational Schema
     */
    protected void createRCFRulesBasisSchema() {

        String dropPropertiesTable = "DROP TABLE IF EXISTS "
                                     + RCF_RULES_BASIS_PROPERTIES;
        String createPropertiesTable = "CREATE TABLE "
                                       + RCF_RULES_BASIS_PROPERTIES + " ("
                                       + RULES_BASIS_ID
                                       + " INT(5) PRIMARY KEY AUTO_INCREMENT, "
                                       + DATASET_NAME
                                       + " VARCHAR(30) NOT NULL, "
                                       + RELATION_NAME
                                       + " VARCHAR(30) NOT NULL REFERENCES "
                                       + RCF_RELATIONS_PROPERTIES + "."
                                       + RELATION_NAME + " ON DELETE CASCADE, "
                                       + MIN_SUPPORT
                                       + " DECIMAL(3,2) NOT NULL, "
                                       + MIN_CONFIDENCE
                                       + " DECIMAL(3,2) NOT NULL)";

        String dropRulesBasisTable = "DROP TABLE IF EXISTS " + RCF_RULES_BASIS;
        String createRulesBasisTable = "CREATE TABLE " + RCF_RULES_BASIS + " ("
                                       + RULES_BASIS_ID
                                       + " INT(5) NOT NULL REFERENCES "
                                       + RCF_RULES_BASIS_PROPERTIES
                                       + " ON DELETE CASCADE, " + PREMISE
                                       + " VARCHAR(200) NOT NULL, "
                                       + CONSEQUENCE
                                       + " VARCHAR(200) NOT NULL, " + SUPPORT
                                       + " DECIMAL(3,2), " + CONFIDENCE
                                       + " DECIMAL(3,2), " + "PRIMARY KEY ("
                                       + RULES_BASIS_ID + ", " + PREMISE + ", "
                                       + CONSEQUENCE + "))";

        try {
            stat = dbc.getConnection().createStatement();
            stat.executeUpdate(dropPropertiesTable);
            stat.executeUpdate(createPropertiesTable);
            stat.executeUpdate(dropRulesBasisTable);
            stat.executeUpdate(createRulesBasisTable);
        } catch (Exception e) {
            System.err.println("Error creating the RCF Rules Basis Schema");
            e.printStackTrace();
        }
    }

    /**
     * A method to add a rules basis to the database
     */
    public void addRulesBasis(String dataset, String relName, Set<Rule> rules,
                              double minSupport, double minConfidence) {

        String insertProperties = "INSERT INTO " + RCF_RULES_BASIS_PROPERTIES
                                  + " (" + DATASET_NAME + ", " + RELATION_NAME
                                  + ", " + MIN_SUPPORT + ", " + MIN_CONFIDENCE
                                  + ") VALUES ('" + dataset + "', '" + relName
                                  + "', " + minSupport + ", " + minConfidence
                                  + ")";

        String insertRuleGeneric = "INSERT INTO " + RCF_RULES_BASIS
                                   + " VALUES (LAST_INSERT_ID(), ";

        try {
            stat = dbc.getConnection().createStatement();
            stat.executeUpdate(insertProperties);

            Iterator<Rule> rulesIterator = rules.iterator();
            while (rulesIterator.hasNext()) {

                String insertRule = insertRuleGeneric;
                Rule currentRule = rulesIterator.next();
                Iterator<FormalAttribute> premiseIterator = currentRule
                        .getAntecedent().iterator();
                Iterator<FormalAttribute> consequenceIterator = currentRule
                        .getConsequence().iterator();

                String premises = "";
                if (premiseIterator.hasNext()) {
                    premises += filterAttName(((Object) premiseIterator.next())
                            .toString());
                }
                while (premiseIterator.hasNext()) {
                    premises += SEPARATOR
                                + filterAttName(((Object) premiseIterator
                                        .next()).toString());
                }
                insertRule += "'" + premises + "', ";

                String consequences = "";
                if (consequenceIterator.hasNext()) {
                    consequences += filterAttName(((Object) consequenceIterator
                            .next()).toString());
                }
                while (consequenceIterator.hasNext()) {
                    consequences += SEPARATOR
                                    + filterAttName(((Object) consequenceIterator
                                            .next()).toString());
                }
                insertRule += "'"
                              + consequences
                              + "', "
                              + Double.toString(((double) ((int) (currentRule
                                      .getSupport() * 100.0))) / 100.0)
                              + ", "
                              + Double.toString(((double) ((int) (currentRule
                                      .getConfiance() * 100.0))) / 100.0) + ")";

                stat.executeUpdate(insertRule);
            }

        } catch (Exception e) {
            System.err.println("Error adding a dataset to the rules table");
        }
    }

    /**
     * A method to delete a list of rules basis from the database
     */
    public void deleteRulesBasis(Vector rulesBasisIDs) {
        for (int i = 0; i < rulesBasisIDs.size(); i++) {
            deleteRulesBasis(rulesBasisIDs.get(i).toString());
        }
    }

    /**
     * A method to delete a single rules basis from the database with its ID
     */
    public void deleteRulesBasis(String rulesBasisID) {

        try {
            stat = dbc.getConnection().createStatement();
            stat.executeUpdate("DELETE FROM " + RCF_RULES_BASIS + " WHERE "
                               + RULES_BASIS_ID + " = " + rulesBasisID);
            stat.executeUpdate("DELETE FROM " + RCF_RULES_BASIS_PROPERTIES
                               + " WHERE " + RULES_BASIS_ID + " = "
                               + rulesBasisID);

        } catch (Exception e) {
            System.err.println("Error deleting the rules basis '"
                               + rulesBasisID + "'");
        }
    }

    /**
     * A method to get the list of rules basis IDs associated to a certain
     * relation from the database
     */
    public Vector getRulesBasisIDsOfRelation(String relName) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + RULES_BASIS_ID + " FROM "
                                   + RCF_RULES_BASIS_PROPERTIES + " WHERE "
                                   + RELATION_NAME + " = '" + relName + "'");
            Vector result = new Vector();
            while (rs.next()) {
                result.addElement(rs.getString(1));
            }
            return result;
        } catch (Exception e) {
            System.err.println("Error getting the rules basis related to '"
                               + relName + "'");
        }
        return null;
    }

    /**
     * A method to get the list of all the rules basis from the database
     */
    public Vector getAllRulesBasisList() {

        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + RULES_BASIS_ID + ", "
                                   + DATASET_NAME + ", " + RELATION_NAME + ", "
                                   + MIN_SUPPORT + ", " + MIN_CONFIDENCE
                                   + " FROM " + RCF_RULES_BASIS_PROPERTIES);
            Vector rulesBasis = new Vector();
            while (rs.next()) {
                rulesBasis.addElement("ID #" + rs.getString(1) + " ["
                                      + rs.getString(2) + ", "
                                      + rs.getString(3) + ", "
                                      + rs.getString(4) + ", "
                                      + rs.getString(5) + "]");
            }
            return rulesBasis;
        } catch (Exception e) {
            System.err.println("Error getting the rules basis list");
        }
        return null;
    }

    /**
     * A method to get the list of rules basis associated to a certain relation
     * from the database
     */
    public Vector getRelationRulesBasisList(String relName) {

        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + RULES_BASIS_ID + ", "
                                   + DATASET_NAME + ", " + MIN_SUPPORT + ", "
                                   + MIN_CONFIDENCE + " FROM "
                                   + RCF_RULES_BASIS_PROPERTIES + " WHERE "
                                   + RELATION_NAME + " = '" + relName + "'");
            Vector rulesBasis = new Vector();
            while (rs.next()) {
                rulesBasis.addElement("ID #" + rs.getString(1) + " ["
                                      + rs.getString(2) + ", " + relName + ", "
                                      + rs.getString(3) + ", "
                                      + rs.getString(4) + "]");
            }
            return rulesBasis;
        } catch (Exception e) {
            System.err.println("Error getting the relation rules basis list");
        }
        return null;
    }

    /**
     * A method to get the rules of a rules basis from the database
     */
    public Set<Rule> getRules(String rulesBasisID) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + PREMISE + ", " + CONSEQUENCE
                                   + ", " + SUPPORT + ", " + CONFIDENCE
                                   + " FROM " + RCF_RULES_BASIS + " WHERE "
                                   + RULES_BASIS_ID + " = " + rulesBasisID);
            Set<Rule> result = new HashSet<Rule>();
            while (rs.next()) {

                Intent premise = new BGIntent();
                Intent consequence = new BGIntent();

                StringTokenizer premiseTokenizer = new StringTokenizer(
                                                                       rs.getString(1),
                                                                       SEPARATOR);
                StringTokenizer consequenceTokenizer = new StringTokenizer(
                                                                           rs.getString(2),
                                                                           SEPARATOR);

                while (premiseTokenizer.hasMoreTokens()) {
                    premise.add(new DefaultFormalAttribute(premiseTokenizer
                            .nextToken()));
                }

                while (consequenceTokenizer.hasMoreTokens()) {
                    consequence
                            .add(new DefaultFormalAttribute(
                                                            consequenceTokenizer
                                                                    .nextToken()));
                }

                result.add(new Rule(premise, consequence, Double.parseDouble(rs
                        .getString(3)), Double.parseDouble(rs.getString(4))));
            }
            return result;

        } catch (Exception e) {
            System.err.println("Error getting the rules");
        }
        return null;
    }

    /**
     * A method to get the given dataset name of a rules basis from the database
     */
    public String getDatasetName(String rulesBasisID) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + DATASET_NAME + " FROM "
                                   + RCF_RULES_BASIS_PROPERTIES + " WHERE "
                                   + RULES_BASIS_ID + " = " + rulesBasisID);
            rs.first();
            if (rs.last()) {
                return rs.getString(1);
            }
        } catch (Exception e) {
            System.err
                    .println("Error getting the dataset name of rules basis '"
                             + rulesBasisID + "'");
        }
        return null;
    }

    /**
     * A method to get the minimal confidence of a rules basis from the database
     */
    public double getMinConfidence(String rulesBasisID) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + MIN_CONFIDENCE + " FROM "
                                   + RCF_RULES_BASIS_PROPERTIES + " WHERE "
                                   + RULES_BASIS_ID + " = " + rulesBasisID);
            rs.first();
            if (rs.last()) {
                return Double.parseDouble(rs.getString(1));
            }
        } catch (Exception e) {
            System.err
                    .println("Error getting the minimal confidence of rules basis '"
                             + rulesBasisID + "'");
        }
        return 0.0;
    }

    /**
     * A method to get the minimal support of a rules basis from the database
     */
    public double getMinSupport(String rulesBasisID) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + MIN_SUPPORT + " FROM "
                                   + RCF_RULES_BASIS_PROPERTIES + " WHERE "
                                   + RULES_BASIS_ID + " = " + rulesBasisID);

            rs.first();
            if (rs.last()) {
                return Double.parseDouble(rs.getString(1));
            }

        } catch (Exception e) {
            System.err
                    .println("Error getting the minimal support of rules basis '"
                             + rulesBasisID + "'");
        }
        return 0.0;
    }

    /*********************************************************************/
    /** LATTICES **/
    /*********************************************************************/

    /**
     * A method to create the Lattices Relational Schema in the database
     * (creates the tables)
     */
    protected void createRCFLatticesSchema() {

        String dropLatticesProperties = "DROP TABLE IF EXISTS "
                                        + RCF_LATTICES_PROPERTIES;
        String createLatticesProperties = "CREATE TABLE "
                                          + RCF_LATTICES_PROPERTIES
                                          + " ("
                                          + LATTICE_ID
                                          + " INT(5) PRIMARY KEY AUTO_INCREMENT, "
                                          + RELATION_NAME
                                          + " VARCHAR(30) NOT NULL REFERENCES "
                                          + RCF_RELATIONS_PROPERTIES + "."
                                          + RELATION_NAME
                                          + " ON DELETE CASCADE, "
                                          + LATTICE_DESCRIPTION
                                          + " VARCHAR(200), " + LATTICE_TYPE
                                          + " VARCHAR(30), " + MIN_SUPPORT
                                          + " DECIMAL(3,2), "
                                          + LATTICE_TOP_NODE + " INT(5), "
                                          + LATTICE_BOTTOM_NODE + " INT(5))";

        String dropLatticesNodes = "DROP TABLE IF EXISTS " + RCF_LATTICES_NODES;
        String createLatticesNodes = "CREATE TABLE " + RCF_LATTICES_NODES
                                     + " (" + LATTICE_ID
                                     + " INT(5) NOT NULL REFERENCES "
                                     + RCF_LATTICES_PROPERTIES
                                     + " ON DELETE CASCADE, " + LATTICE_NODE
                                     + " INT(5) NOT NULL, " + " PRIMARY KEY ("
                                     + LATTICE_ID + ", " + LATTICE_NODE + "))";

        String dropLatticesParents = "DROP TABLE IF EXISTS "
                                     + RCF_LATTICES_PARENTS;
        String createLatticesParents = "CREATE TABLE " + RCF_LATTICES_PARENTS
                                       + " (" + LATTICE_ID
                                       + " INT(5) NOT NULL REFERENCES "
                                       + RCF_LATTICES_PROPERTIES
                                       + " ON DELETE CASCADE, " + LATTICE_NODE
                                       + " INT(5) NOT NULL, " + PARENT_NODE
                                       + " INT(5) NOT NULL, "
                                       + " PRIMARY KEY (" + LATTICE_ID + ", "
                                       + LATTICE_NODE + ", " + PARENT_NODE
                                       + "))";

        String dropLatticesExtents = "DROP TABLE IF EXISTS "
                                     + RCF_LATTICES_EXTENTS;
        String createLatticesExtents = "CREATE TABLE " + RCF_LATTICES_EXTENTS
                                       + " (" + LATTICE_ID
                                       + " INT(5) NOT NULL REFERENCES "
                                       + RCF_RELATIONS_PROPERTIES + "."
                                       + RELATION_NAME + " ON DELETE CASCADE, "
                                       + LATTICE_NODE + " INT(5) NOT NULL, "
                                       + LATTICE_OBJECT
                                       + " VARCHAR(30) NOT NULL, "
                                       + "PRIMARY KEY (" + LATTICE_ID + ", "
                                       + LATTICE_NODE + ", " + LATTICE_OBJECT
                                       + "))";

        String dropLatticesIntents = "DROP TABLE IF EXISTS "
                                     + RCF_LATTICES_INTENTS;
        String createLatticesIntents = "CREATE TABLE " + RCF_LATTICES_INTENTS
                                       + " (" + LATTICE_ID
                                       + " INT(5) NOT NULL REFERENCES "
                                       + RCF_RELATIONS_PROPERTIES + "."
                                       + RELATION_NAME + " ON DELETE CASCADE, "
                                       + LATTICE_NODE + " INT(5) NOT NULL, "
                                       + LATTICE_ATTRIBUTE
                                       + " VARCHAR(30) NOT NULL, "
                                       + "PRIMARY KEY (" + LATTICE_ID + ", "
                                       + LATTICE_NODE + ", "
                                       + LATTICE_ATTRIBUTE + "))";

        String dropLatticesGenerators = "DROP TABLE IF EXISTS "
                                        + RCF_LATTICES_GENERATORS;
        String createLatticesGenerators = "CREATE TABLE "
                                          + RCF_LATTICES_GENERATORS + " ("
                                          + LATTICE_ID
                                          + " INT(5) NOT NULL REFERENCES "
                                          + RCF_RELATIONS_PROPERTIES + "."
                                          + RELATION_NAME
                                          + " ON DELETE CASCADE, "
                                          + LATTICE_NODE + " INT(5) NOT NULL, "
                                          + LATTICE_GENERATOR
                                          + " INT(5) NOT NULL, "
                                          + LATTICE_ATTRIBUTE
                                          + " VARCHAR(30) NOT NULL, "
                                          + "PRIMARY KEY (" + LATTICE_ID + ", "
                                          + LATTICE_NODE + ", "
                                          + LATTICE_GENERATOR + ", "
                                          + LATTICE_ATTRIBUTE + "))";

        try {
            stat = dbc.getConnection().createStatement();
            stat.executeUpdate(dropLatticesProperties);
            stat.executeUpdate(createLatticesProperties);
            stat.executeUpdate(dropLatticesNodes);
            stat.executeUpdate(createLatticesNodes);
            stat.executeUpdate(dropLatticesParents);
            stat.executeUpdate(createLatticesParents);
            stat.executeUpdate(dropLatticesExtents);
            stat.executeUpdate(createLatticesExtents);
            stat.executeUpdate(dropLatticesIntents);
            stat.executeUpdate(createLatticesIntents);
            stat.executeUpdate(dropLatticesGenerators);
            stat.executeUpdate(createLatticesGenerators);
        } catch (Exception e) {
            System.err.println("Error creating the RCF Lattices Schema");
            e.printStackTrace();
        }

    }

    /**
     * A method to save in the databsae the currently associated lattice of a
     * relation
     */
    public void saveLattice(RelationBuilder absRel) {

        try {

            stat = dbc.getConnection().createStatement();

            CompleteConceptLattice lattice = absRel.getLattice();
            String relName = DatabaseFunctions.filter(absRel.getName());
            String description = lattice.getDescription();
            String minSupport = new Double(lattice.getMinSupp()).toString();
            String topNode = "0";
            String bottomNode = "" + (lattice.size() - 1);

            String type = "Undefined";
            if (lattice instanceof LatticeGraph) {
                type = "LatticeGraph";
            } else if (lattice instanceof CompleteConceptLatticeImp) {
                type = "ConceptLattice";
            }

            String insertProperties = "INSERT INTO " + RCF_LATTICES_PROPERTIES
                                      + " (" + RELATION_NAME + ", "
                                      + LATTICE_DESCRIPTION + ", "
                                      + LATTICE_TYPE + ", " + MIN_SUPPORT
                                      + ", " + LATTICE_TOP_NODE + ", "
                                      + LATTICE_BOTTOM_NODE + ") VALUES ('"
                                      + relName + "', '" + description + "', '"
                                      + type + "', " + minSupport + ", "
                                      + topNode + ", " + bottomNode + ")";

            stat.executeUpdate(insertProperties);

            String insertNodeGeneric = "INSERT INTO " + RCF_LATTICES_NODES
                                       + " VALUES (LAST_INSERT_ID(), ";
            String insertParentGeneric = "INSERT INTO " + RCF_LATTICES_PARENTS
                                         + " VALUES (LAST_INSERT_ID(), ";
            String insertExtentGeneric = "INSERT INTO " + RCF_LATTICES_EXTENTS
                                         + " VALUES (LAST_INSERT_ID(), ";
            String insertIntentGeneric = "INSERT INTO " + RCF_LATTICES_INTENTS
                                         + " VALUES (LAST_INSERT_ID(), ";
            String insertGeneratorGeneric = "INSERT INTO "
                                            + RCF_LATTICES_GENERATORS
                                            + " VALUES (LAST_INSERT_ID(), ";

            lattice.getTop().resetDegre();
            int nextIdNode = 0;
            Hashtable correspId = new Hashtable();
            Vector Q = new Vector();
            Q.add(lattice.getTop());
            ConceptNode nodeToWrite;

            while (Q.size() != 0) {
                nodeToWrite = (ConceptNode) Q.remove(0);

                // Node
                String latticeNode = "" + nextIdNode;
                correspId.put(nodeToWrite.getId(), new Integer(nextIdNode));
                nextIdNode++;

                stat.executeUpdate(insertNodeGeneric + latticeNode + ")");

                // Extent
                for (Iterator it = nodeToWrite.getContent().getExtent()
                        .iterator(); it.hasNext();) {
                    String object = filterObjName(((FormalObject) it.next())
                            .toString());
                    stat.executeUpdate(insertExtentGeneric + latticeNode
                                       + ", '" + object + "')");
                }

                // Intent
                for (Iterator it = nodeToWrite.getContent().getIntent()
                        .iterator(); it.hasNext();) {
                    String attribute = filterAttName(((FormalAttribute) it
                            .next()).toString());
                    stat.executeUpdate(insertIntentGeneric + latticeNode
                                       + ", '" + attribute + "')");
                }

                // Parents
                for (Iterator it = nodeToWrite.getParents().iterator(); it
                        .hasNext();) {
                    String parentNode = ((Integer) correspId
                            .get(((ConceptNode) it.next()).getId())).toString();
                    stat.executeUpdate(insertParentGeneric + latticeNode + ", "
                                       + parentNode + ")");
                }

                // Generators
                if (nodeToWrite.getContent().getGenerator().size() != 0) {
                    int generator = 0;
                    for (Iterator it = nodeToWrite.getContent().getGenerator()
                            .iterator(); it.hasNext();) {
                        for (Iterator itG = ((Intent) it.next()).iterator(); itG
                                .hasNext();) {
                            String attribute = filterAttName(((FormalAttribute) itG
                                    .next()).toString());
                            stat.executeUpdate(insertGeneratorGeneric
                                               + latticeNode + ", " + generator
                                               + ", '" + attribute + "')");
                        }
                        generator++;
                    }
                }

                // Linear extension
                for (Iterator it = nodeToWrite.getChildren().iterator(); it
                        .hasNext();) {
                    ConceptNode P = (ConceptNode) it.next();
                    if (P.getDegre() == -1) {
                        P.setDegre(P.getParents().size());
                    }
                    P.setDegre(P.getDegre() - 1);
                    if (P.getDegre() == 0) {
                        Q.add(P);
                    }
                }
            }
            String latticeNode = "" + (nextIdNode - 1);
            stat.executeUpdate("UPDATE " + RCF_LATTICES_PROPERTIES + " SET "
                               + LATTICE_BOTTOM_NODE + " = " + latticeNode
                               + " WHERE " + LATTICE_ID + " = LAST_INSERT_ID()");
        } catch (Exception e) {
            System.err.println("Error adding a lattice to the database");
            e.printStackTrace();
        }
    }

    /**
     * A method to delete a list of lattices from the database
     */
    public void deleteLattices(Vector lattices) {
        for (int i = 0; i < lattices.size(); i++) {
            deleteLattice(lattices.get(i).toString());
        }
    }

    /**
     * A method to delete a lattice from the database with its ID
     */
    public void deleteLattice(String latticeID) {

        try {
            stat = dbc.getConnection().createStatement();
            stat.executeUpdate("DELETE FROM " + RCF_LATTICES_EXTENTS
                               + " WHERE " + LATTICE_ID + " = " + latticeID);
            stat.executeUpdate("DELETE FROM " + RCF_LATTICES_INTENTS
                               + " WHERE " + LATTICE_ID + " = " + latticeID);
            stat.executeUpdate("DELETE FROM " + RCF_LATTICES_GENERATORS
                               + " WHERE " + LATTICE_ID + " = " + latticeID);
            stat.executeUpdate("DELETE FROM " + RCF_LATTICES_NODES + " WHERE "
                               + LATTICE_ID + " = " + latticeID);
            stat.executeUpdate("DELETE FROM " + RCF_LATTICES_PARENTS
                               + " WHERE " + LATTICE_ID + " = " + latticeID);
            stat.executeUpdate("DELETE FROM " + RCF_LATTICES_PROPERTIES
                               + " WHERE " + LATTICE_ID + " = " + latticeID);

        } catch (Exception e) {
            System.err
                    .println("Error deleting the lattice '" + latticeID + "'");
            e.printStackTrace();
        }
    }

    public Vector getRelationLatticesList(String relName) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + LATTICE_ID + ", "
                                   + LATTICE_DESCRIPTION + " FROM "
                                   + RCF_LATTICES_PROPERTIES + " WHERE "
                                   + RELATION_NAME + " = '" + relName + "'");
            Vector lattices = new Vector();
            while (rs.next()) {
                lattices.addElement("ID #" + rs.getString(1) + " ["
                                    + rs.getString(2) + "]");
            }
            return lattices;
        } catch (Exception e) {
            System.err
                    .println("Error getting the lattices list for the relation '"
                             + relName + "'");
            e.printStackTrace();
        }
        return null;
    }

    public Vector getAllLatticesList() {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + LATTICE_ID + ", "
                                   + LATTICE_DESCRIPTION + " FROM "
                                   + RCF_LATTICES_PROPERTIES);
            Vector lattices = new Vector();
            while (rs.next()) {
                lattices.addElement("ID #" + rs.getString(1) + " ["
                                    + rs.getString(2) + "]");
            }
            return lattices;
        } catch (Exception e) {
            System.err.println("Error getting the lattices list");
        }
        return null;
    }

    protected String getLatticeProperty(String latticeID, String property) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + property + " FROM "
                                   + RCF_LATTICES_PROPERTIES + " WHERE "
                                   + LATTICE_ID + " = " + latticeID);
            rs.first();
            if (rs.isLast()) {
                return rs.getString(1);
            }
        } catch (Exception e) {
            System.err.println("Error getting the lattice property");
            e.printStackTrace();
        }
        return null;
    }

    protected Vector getLatticeNodesList(String latticeID) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + LATTICE_NODE + " FROM "
                                   + RCF_LATTICES_NODES + " WHERE "
                                   + LATTICE_ID + " = " + latticeID);
            Vector nodes = new Vector();
            while (rs.next()) {
                nodes.add(rs.getString(1));
            }
            return nodes;

        } catch (Exception e) {
            System.err.println("Error getting the lattice nodes list");
            e.printStackTrace();
        }
        return null;
    }

    protected Vector getLatticeNodeExtent(String latticeID, String nodeName) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + LATTICE_OBJECT + " FROM "
                                   + RCF_LATTICES_EXTENTS + " WHERE "
                                   + LATTICE_ID + " = " + latticeID + " AND "
                                   + LATTICE_NODE + " = " + nodeName);
            Vector extent = new Vector();
            while (rs.next()) {
                extent.add(new DefaultFormalObject(rs.getString(1)));
            }
            return extent;

        } catch (Exception e) {
            System.err.println("Error getting the lattice node extent");
            e.printStackTrace();
        }
        return null;
    }

    protected Vector getLatticeNodeIntent(String latticeID, String nodeName) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + LATTICE_ATTRIBUTE + " FROM "
                                   + RCF_LATTICES_INTENTS + " WHERE "
                                   + LATTICE_ID + " = " + latticeID + " AND "
                                   + LATTICE_NODE + " = " + nodeName);
            Vector intent = new Vector();
            while (rs.next()) {
                intent.add(new DefaultFormalAttribute(rs.getString(1)));
            }
            return intent;

        } catch (Exception e) {
            System.err.println("Error getting the lattice node intent");
            e.printStackTrace();
        }
        return null;
    }

    protected Vector getLatticeNodeParents(String latticeID, String nodeName) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + PARENT_NODE + " FROM "
                                   + RCF_LATTICES_PARENTS + " WHERE "
                                   + LATTICE_ID + " = " + latticeID + " AND "
                                   + LATTICE_NODE + " = " + nodeName);
            Vector parents = new Vector();
            while (rs.next()) {
                parents.add(rs.getString(1));
            }
            return parents;

        } catch (Exception e) {
            System.err.println("Error getting the lattice node parents");
            e.printStackTrace();
        }
        return null;
    }

    protected Vector getLatticeNodeGenerators(String latticeID, String nodeName) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + LATTICE_GENERATOR + ", "
                                   + LATTICE_ATTRIBUTE + " FROM "
                                   + RCF_LATTICES_GENERATORS + " WHERE "
                                   + LATTICE_ID + " = " + latticeID + " AND "
                                   + LATTICE_NODE + " = " + nodeName);

            Vector generators = new Vector();
            while (rs.next()) {
                String gen = rs.getString(1);
                Intent attributes = new SetIntent();
                attributes.add(new DefaultFormalAttribute(rs.getString(2)));
                while (rs.next() && gen.equals(rs.getString(1))) {
                    attributes.add(new DefaultFormalAttribute(rs.getString(2)));
                }
                generators.add(attributes);
                rs.previous();
            }
            return generators;

        } catch (Exception e) {
            System.err.println("Error getting the lattice node generators");
            e.printStackTrace();
        }
        return null;
    }

    protected String getTopNodeID(String latticeID) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + LATTICE_TOP_NODE + " FROM "
                                   + RCF_LATTICES_PROPERTIES + " WHERE "
                                   + LATTICE_ID + " = " + latticeID);
            rs.first();
            if (rs.last()) {
                return rs.getString(1);
            }
        } catch (Exception e) {
            System.err.println("Error getting the top node");
            e.printStackTrace();
        }
        return null;
    }

    protected String getBottomNodeID(String latticeID) {
        try {
            stat = dbc.getConnection().createStatement();
            rs = stat.executeQuery("SELECT " + LATTICE_BOTTOM_NODE + " FROM "
                                   + RCF_LATTICES_PROPERTIES + " WHERE "
                                   + LATTICE_ID + " = " + latticeID);
            rs.first();
            if (rs.last()) {
                return rs.getString(1);
            }
        } catch (Exception e) {
            System.err.println("Error getting the bottom node");
            e.printStackTrace();
        }
        return null;
    }

    /**
     * Construct the lattice object from the lattice ID in the database
     */
    public CompleteConceptLattice getLattice(String latticeID) {

        CompleteConceptLattice lattice = null;

        String relName = getLatticeProperty(latticeID, RELATION_NAME);
        String type = getLatticeProperty(latticeID, LATTICE_TYPE);
        String description = getLatticeProperty(latticeID, LATTICE_DESCRIPTION);
        double minSupport = (double) Double
                .parseDouble(getLatticeProperty(latticeID, MIN_SUPPORT));
        String topNode = getTopNodeID(latticeID);
        String bottomNode = getBottomNodeID(latticeID);

        if (type == null) {
            return null;
        } else if (type.equals("ConceptLattice")) {
            lattice = new CompleteConceptLatticeImp();
        } else if (type.equals("LatticeGraph")) {
            lattice = new LatticeGraph();
        } else {
            return null;
        }

        Vector processedNodes = new Vector();
        Vector nodes = getLatticeNodesList(latticeID);
        boolean firstNode = true;

        for (int i = 0; i < nodes.size(); i++) {

            String nodeName = (String) nodes.get(i);
            Extent extent = new SetExtent();
            Intent intent = new SetIntent();
            extent.addAll(getLatticeNodeExtent(latticeID, nodeName));
            intent.addAll(getLatticeNodeIntent(latticeID, nodeName));
            ConceptNode newNode = new ConceptNodeImp(new Integer(nodeName),
                                                     new ConceptImp(extent,
                                                                    intent));

            Vector generators = getLatticeNodeGenerators(latticeID, nodeName);
            if (generators != null) {
                newNode.getContent().setGenerator(generators);
            }
            if (bottomNode != null && bottomNode.equals(nodeName)) {
                lattice.setBottom(newNode);
            }

            if (firstNode) {
                lattice.setTop(newNode);
                firstNode = false;
                if (lattice instanceof CompleteConceptLatticeImp) {
                    ((CompleteConceptLatticeImp) lattice).incNbOfNodes();
                }

            } else {
                Vector parentNodes = getLatticeNodeParents(latticeID, nodeName);
                for (int j = 0; j < parentNodes.size(); j++) {
                    ConceptNode supNode = (ConceptNode) processedNodes
                            .get(Integer.parseInt((String) parentNodes.get(j)));
                    newNode.addParent(supNode);
                    supNode.addChild(newNode);
                }
                if (lattice instanceof LatticeGraph) {
                    ((LatticeGraph) lattice).add(newNode);
                }
                if (lattice instanceof CompleteConceptLatticeImp) {
                    ((CompleteConceptLatticeImp) lattice).incNbOfNodes();
                }
            }
            processedNodes.addElement(newNode);
        }
        lattice.setDescription(description);
        lattice.setMinSupp(minSupport);
        return lattice;
    }

    /*********************************************************************/
    /** UTILS **/
    /*********************************************************************/

    /**
     * A method to change the default object name (to avoid a bug)
     */
    private static String filterObjName(String obj) {
        if (obj.substring(0, 4).equals("obj_")) {
            obj = "obj " + obj.substring(4, obj.length());
        }
        return obj;
    }

    /**
     * A method to change the default attribute name (to avoid a bug)
     */
    private static String filterAttName(String att) {
        if (att.substring(0, 4).equals("att_")) {
            att = "att " + att.substring(4, att.length());
        }
        return att;
    }

    /**
     * A method to perform a direct SQL update (for expert users only)
     */
    public void sqlUpdate(String query) {
        try {
            stat = dbc.getConnection().createStatement();
            stat.executeUpdate(query);
        } catch (Exception e) {
            System.err.println("Error executing the update");
        }
    }

    /**
     * Closes the connection
     */
    public void closeConnection() {
        try {
            if (stat != null)
                stat.close();
            if (rs != null)
                rs.close();
            dbc.closeConnection();
        } catch (Exception e) {
            System.err.println("Error closing the connection");
        }
    }
}
