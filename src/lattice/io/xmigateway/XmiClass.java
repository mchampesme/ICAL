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
 * Created on Jun 26, 2004
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package lattice.io.xmigateway;

import java.util.ArrayList;
import java.util.Iterator;

/**
 * @author rouanehm
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class XmiClass extends XmiElement {
	
	private ArrayList xmiAttributes;
	private ArrayList xmiAssociations;
	
	public XmiClass(String id, String className) {
		super(id,className);
		xmiAttributes=null;
		xmiAssociations=null;
	}
	
	void setXMIAttributes(ArrayList attrs){
		xmiAttributes=attrs;
	}
	
	public void displayContents(){
		System.out.print("          * Class: "+name+"\n");
		Iterator it;
		if(xmiAttributes!=null){
			System.out.print("                     Attributes are:\n");
			it=xmiAttributes.iterator();
			while(it.hasNext()) {
				XmiAttribute currentAttr=(XmiAttribute) it.next();
				currentAttr.displayContents();
			}	
		}
		if(xmiAssociations!=null){
			System.out.print("                     Associations are:\n");
			it=xmiAssociations.iterator();
			while(it.hasNext()) {
				XmiAssociation currentAttr=(XmiAssociation) it.next();
				currentAttr.displayContents();
			}
		}
	}

	public int getNumberOfAttributes() {		
		return xmiAttributes.size();
	}
	
	public ArrayList getAttributes() {
		return xmiAttributes;
	}
}
