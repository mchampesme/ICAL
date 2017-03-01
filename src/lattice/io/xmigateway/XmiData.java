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
public class XmiData {

	private String modelName;
	private ArrayList xmiClasses;
	// the set of the attributes that will be used for the classes
	// notice that this can be different to the set of all attributes 
	// due to repetition (synonimy) 
	private ArrayList effectiveAttributes; 
	private ArrayList xmiAssociations;
	private ArrayList xmiConstraints;
	
	public XmiData(){
		modelName="";
		xmiClasses = new ArrayList();
		xmiAssociations = new ArrayList();
		xmiConstraints = new ArrayList();
		effectiveAttributes = null;
	}
	
	public void displayContents(){
		System.out.print("Family Name: "+modelName+"\n");
		System.out.print("Context of classes has: \n");
		Iterator it=xmiClasses.iterator();
		while(it.hasNext()) {
			XmiClass currentClass=(XmiClass) it.next();
			currentClass.displayContents();
		}
		System.out.print("Context of associations has: \n");
		it=xmiAssociations.iterator();
		while(it.hasNext()) {
			XmiAssociation currentAssoc=(XmiAssociation) it.next();
			currentAssoc.displayContents();
		}			
	}
	void setModelName(String name){
		modelName=name;
	}
	void appendClass(XmiClass xmiclass){
		xmiClasses.add(xmiclass);
	}
	
	void appendAssoc(XmiAssociation xmiassoc){
		xmiAssociations.add(xmiassoc);
	}

	public String getClass(String classID) {
		Iterator it=xmiClasses.iterator();
		while(it.hasNext()) {
			XmiClass currentClass=(XmiClass) it.next();
			if(currentClass.getClassID().compareTo(classID)==0) return currentClass.getName(); 
		}
		return "NOTFOUND";				
	}

	public String getModelName() {
		return modelName;		
	}

	public int getNumberOfClasses() {
			return xmiClasses.size();		
	}
	
	public int getNumberOfAssocs() {
		return xmiAssociations.size();		
	}
	
	public int getNumberOfAttributes() {
		int attrs=0;
		Iterator it=xmiClasses.iterator();
		while(it.hasNext()) {
			XmiClass currentClass=(XmiClass) it.next();
			attrs=attrs+currentClass.getNumberOfAttributes();
		}
		return attrs;			
	}
	
	public ArrayList getEffectiveAttributes() {
		if(effectiveAttributes==null) effectiveAttributes = computeEffectiveAttributes();
		return effectiveAttributes;
	}
	
	public XmiClass getClass(int index) { return (XmiClass) xmiClasses.get(index); }
	public XmiAssociation getAssociation(int index) { return (XmiAssociation) xmiAssociations.get(index); }
	
	private ArrayList computeEffectiveAttributes(){
		if(effectiveAttributes==null){
			effectiveAttributes = new ArrayList();
			Iterator classesIt=xmiClasses.iterator();
			while(classesIt.hasNext()) {
				XmiClass currentClass=(XmiClass) classesIt.next();
				ArrayList classAttrs=currentClass.getAttributes();
				if(classAttrs!=null){
					Iterator attrsIt=classAttrs.iterator();				 
					while(attrsIt.hasNext()) {
						XmiAttribute currentAttr=(XmiAttribute) attrsIt.next();
						if(!exist(effectiveAttributes,currentAttr)) effectiveAttributes.add(currentAttr);
					}//while
				}//if 
			}
			return effectiveAttributes;
	}
	else return effectiveAttributes;
}

	private boolean exist(ArrayList setOfXMIElements, XmiElement element) {
		Iterator elementsIt= setOfXMIElements.iterator();
		while(elementsIt.hasNext()) {
			XmiElement currentElement=(XmiElement) elementsIt.next();
			String str1 = currentElement.getName();
			String str2 = element.getName();
			if(str1.compareTo(str2)==0) return true;
		}
		return false;
	}
}