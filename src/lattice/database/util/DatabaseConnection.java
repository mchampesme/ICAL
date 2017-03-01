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
 * Created on 2004-06-08
 * @author Manuel Aupetit
 */
package lattice.database.util;

import java.sql.Connection;
import java.sql.DriverManager;

/**
 * This class configures the connection to the database.<br>
 * It uses default parameters, which can of course be changed at every execution of Galicia.<br>
 * But as the default parameters will always be those below, the user should edit this class and change them.
 * @author Manuel Aupetit
 */
public class DatabaseConnection {
	
	private static final String DEFAULT_SERVER = "europa.iro.umontreal.ca";
	private static final String DEFAULT_USERNAME = "aupetitm";
	private static final String DEFAULT_PASSWORD = "galicia";
	private static final String DEFAULT_DATABASE = "aupetitm_default";

	private static String server = DEFAULT_SERVER;
	private static String username = DEFAULT_USERNAME;
	private static String password = DEFAULT_PASSWORD;
	private static String database = DEFAULT_DATABASE;
	private static boolean alwaysUseParameters = false;
	
	private String tableName;
	
	private Connection conn = null;
	
	/**
	 * Default constructor that creates a JDBC connection to a MySQL database, using the default parameters
	 */
	public DatabaseConnection() {
		try {
			Class.forName("com.mysql.jdbc.Driver").newInstance();
			this.conn = DriverManager.getConnection(
										"jdbc:mysql://" +
										DatabaseConnection.server +
										"/" + DatabaseConnection.database +
										"?user=" + DatabaseConnection.username +
										"&password=" + DatabaseConnection.password);
			System.out.println("Connected to '" + DatabaseConnection.server + "' MySQL server");
		} catch (Exception e) {
			System.err.println("Error creating the connection");
		}
	}
	
	
	/**
	 * A method to set the desired parameters for the MySQL connection
	 */
	public static void setParameters(
									String server,
									String username,
									String password,
									String database,
									boolean alwaysUseParameters) {
		DatabaseConnection.server = server;
		DatabaseConnection.username = username;
		DatabaseConnection.password = password;
		DatabaseConnection.database = database;
		DatabaseConnection.alwaysUseParameters = alwaysUseParameters; 
	}
	
	/**
	 * A method to reset the connection parameters to the default ones
	 */
	public static void setDefaultParameters() {
		DatabaseConnection.setParameters(
								DEFAULT_SERVER,
								DEFAULT_USERNAME,
								DEFAULT_PASSWORD,
								DEFAULT_DATABASE,
								true);
	}

	
	/**
	 * A method to set the database name parameter
	 */
	public static void setDatabase(String database) {
		DatabaseConnection.database = database;
	}
	
	/**
	 * A method to set the boolean used to decide if the parameters will be asked again or not
	 * @param b <code>true</code> if the parameters are to be always the same, <code>false</code> if the user wants to edit/see them each time 
	 */
	public static void setAlwaysUseParameters(boolean b) {
		DatabaseConnection.alwaysUseParameters = b;
	}
	
	/**
	 * A method to get the server name
	 */
	public static String getServer() {
		return DatabaseConnection.server;
	}
	
	/**
	 * A method to get the user name
	 */
	public static String getUsername() {
		return DatabaseConnection.username;
	}
	
	/**
	 * A method to get the user password
	 */
	public static String getPassword() {
		return DatabaseConnection.password;
	}
	
	/**
	 * A method to get the database name
	 */
	public static String getDatabase() {
		return DatabaseConnection.database;
	}

	/**
	 * A method to get the relational contexts family name
	 */
	public static String getFamilyName() {
		return database.substring(username.length()+1);
	}
	
	/**
	 * A method to get the state of the <code>alwaysUseParameters</code> boolean
	 */
	public static boolean getAlwaysUseParameters() {
		return DatabaseConnection.alwaysUseParameters;
	}
	
	/**
	 * A method to get the <code>Connection</code> instance created.
	 */
	public Connection getConnection() {
		return this.conn;
	}
	
	/**
	 * A method to close the current connection
	 */
	public void closeConnection() {
		try {
			if (this.conn != null) this.conn.close();
			System.out.println("Connection closed");
		} catch (Exception e) {
			System.err.println("Error closing the connection");
		}
	}
}