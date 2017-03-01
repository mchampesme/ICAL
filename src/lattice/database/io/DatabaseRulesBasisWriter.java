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

import lattice.database.util.DatabaseFunctions;
import lattice.database.util.DatabaseManagement;
import rule.util.RulesBasis;

/**
 * A class to create a rules basis database writer 
 * @author Manuel Aupetit
 */
public class DatabaseRulesBasisWriter extends DatabaseAbstractWriter {

	private DatabaseManagement dbm = null;
	private RulesBasis rulesBasis = null;

	public DatabaseRulesBasisWriter(DatabaseManagement dbm, RulesBasis rulesBasis) {
		this.dbm = dbm;
		this.rulesBasis = rulesBasis;
	}


	public RulesBasis saveRulesBasisToDB() { 
		String relName = DatabaseFunctions.filter(rulesBasis.getAbstractRelation().getName());
		if (DatabaseFunctions.isRelationExisting(dbm, relName)) {
			dbm.addRulesBasis(	rulesBasis.getDatasetName(), relName, rulesBasis.getRules(),
								rulesBasis.getMinSupport(), rulesBasis.getMinConfidence());
		} else {
			DatabaseFunctions.showMessageDialog("Save the relation '" + relName + "' in the database first");
			return null;
		}
		return rulesBasis;
	}


	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		try {
			data = saveRulesBasisToDB();
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
