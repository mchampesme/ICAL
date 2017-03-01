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
 * Created on 2004-09-07
 * @author Manuel Aupetit
 */
package rule.util;

import java.util.Vector;

import lattice.util.concept.Intent;

/**
 * A temporary class to modelise an intent, in order to test the visualization
 * @author Manuel Aupetit
 */
public class IntentInstance {

	protected Intent intent = null;
	protected double support = 0.0;
	
	public IntentInstance(Intent intent, double support) {
		this.intent = intent;
		this.support = support;
	}
	
	public Intent getIntent() {
		return this.intent;
	}
	
	public double getSupport() {
		return this.support;
	}
	
	public String toString() {
		return this.intent.toString() + " " + this.support;
	}
	
}
