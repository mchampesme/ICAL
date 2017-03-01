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

package lattice.util.relation;

import lattice.util.concept.InterObjectBinaryRelationAttribute;


/**
 * @author Mr ROUME
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class InterObjectBinaryRelation extends MatrixBinaryRelationBuilder {
		 
		// the following variable stores the source context of the object-valued attribute
		// the objects of source context are objects in the inter-object relation
		String objectsContextName;
		// the following variable stores the target context of the object-valued attribute		
		// the objects of target context are attributes in the inter-object relation
		String attributesContextName;
	/**
	 * Constructor for InterObjectBinaryRelation.
	 * @param nbObjs
	 * @param nbAtts
	 */
	public InterObjectBinaryRelation(int nbObjs, int nbAtts) {
		super(nbObjs, nbAtts);
		objectsContextName=null;
		attributesContextName=null;
	}

	public InterObjectBinaryRelation(RelationBuilder binRel1, RelationBuilder binRel2) {
		super(binRel1.getObjectsNumber(), binRel2.getObjectsNumber());
		objectsContextName=binRel1.getName();
		attributesContextName=binRel2.getName();	
		for(int i=0;i<getObjectSet().size();i++){
			try{
			getObjectSet().set(i,binRel1.getFormalObject(i)); 
			} catch (Exception e){
				e.printStackTrace();
			}
		}	
		for(int i=0;i<getAttributeSet().size();i++){
			try{
			 getAttributeSet().set(i,new InterObjectBinaryRelationAttribute(binRel2.getFormalObject(i))); 
			} catch (Exception e){
				e.printStackTrace();
			}
		}
		setName("Inter-Object-Relation : "+binRel1.getName()+" / "+binRel2.getName());
	}

	public String getObjectsContextName() {
			return objectsContextName;
	}
	
	public void setObjectsContextName(String name) {
		objectsContextName=name;
	}	

	public String getAttributesContextName() {
			return attributesContextName;
	}
	
	public void setAttributesContextName(String name) {
			attributesContextName=name;
	}
}
