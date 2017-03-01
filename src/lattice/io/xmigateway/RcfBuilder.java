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
 * Created on Jul 1, 2004
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package lattice.io.xmigateway;

import java.util.ArrayList;

import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.DefaultFormalObject;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.RelationalContextFamily;

/**
 * @author rouanehm
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class RcfBuilder {
	
	XmiData xmidata=null;
	RelationalContextFamily rcf=null;
	/**
	 * @param xmidata
	 */
	public RcfBuilder(XmiData xmidata) {
		this.xmidata=xmidata;
		rcf= new RelationalContextFamily(xmidata.getModelName());
	}

	public RelationalContextFamily getRCF(){
		// create context of classes 
		composeClassContext();		
		return rcf;
	}	

	private void composeClassContext() {
		FormalObject fo=null;
		FormalAttribute fa=null;
		MatrixBinaryRelationBuilder classeCtx = new MatrixBinaryRelationBuilder(xmidata.getNumberOfClasses(),
			xmidata.getEffectiveAttributes().size());
		classeCtx.setName("Classes");
		rcf.add(classeCtx);
		// replacing formal objects names
		for(int i =0;i<xmidata.getNumberOfClasses();i++){
			fo=new DefaultFormalObject(xmidata.getClass(i).getName());
			try {
				classeCtx.replaceObject(i,fo);
			} catch (BadInputDataException e) {
				System.out.println("Unable to replace formal objet name in Class context...");
				e.printStackTrace();
			}
		}
		// replacing formal attributes names
		ArrayList attributes=xmidata.getEffectiveAttributes();
		for(int i =0;i<attributes.size();i++){
			fa=new DefaultFormalAttribute(((XmiAttribute)attributes.get(i)).getName());
			try {
				classeCtx.replaceAttribute(i,fa);
			} catch (BadInputDataException e) {
				System.out.println("Unable to replace formal attribute name in Class context...");
				e.printStackTrace();
			}
		}
	}

}
