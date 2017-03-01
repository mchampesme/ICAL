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
 * Created on 2004-06-21
 * @author Manuel Aupetit
 */
package lattice.database.io;

import java.util.Vector;

import lattice.database.util.DatabaseManagement;
import lattice.util.relation.RelationalContextFamily;

/**
 * A class to create a contexts database writer
 * @author Manuel Aupetit
 */
public class DatabaseContextsWriter extends DatabaseAbstractWriter {

	private DatabaseManagement dbm = null;
	private Vector relations = null;
	private RelationalContextFamily relCtxFam = null;
	
	// boolean false if adding relations to a database instead of creating a new one
	private boolean newDatabase = true;


	public DatabaseContextsWriter(DatabaseManagement dbm, Vector relations, RelationalContextFamily relCtxFam, boolean newDatabase) {
		this.dbm = dbm;
		this.relations = relations;
		this.relCtxFam = relCtxFam;
		this.newDatabase = newDatabase;
	}


	public Vector saveFamilyToDB() { 

		if (newDatabase) { // Saving to a new database
			dbm.createRCFSchema(relations, relCtxFam);
		}
		else { // Adding to an existing database
			dbm.addRelationsToRCFSchema(relations, relCtxFam);
		}
		return relations;
	}


	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		try {
			data = saveFamilyToDB();
		} catch (Exception e) {
			if (jobObserv != null) {
			  jobObserv.sendMessage(e.getMessage());
			  jobObserv.jobEnd(false);
			}
			return;
		}
		if (jobObserv != null) jobObserv.jobEnd(true);
	}

}
