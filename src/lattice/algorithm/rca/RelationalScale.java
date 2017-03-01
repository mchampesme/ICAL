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
 * Created on 27-May-2004
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package lattice.algorithm.rca;

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import lattice.util.concept.AbstractFormalAttributeValue;
import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.DefaultFormalObject;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalAttributeValue;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.InterObjectBinaryRelationAttribute;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.structure.ConceptNode;

/**
 * @author rouanehm
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public abstract class RelationalScale {

	private static int WIDE_ENCODING=0;
	private static int NARROW_ENCODING=1;
	private static String relScaleCtxNameSuffix="-scale"; //"-RSCtx";
	
	public RelationalScale(){
	}
	
	/**
	 	 * @param context to whom belong the objects in the inter-object relation rel
	 	 * @param context from whom come the attributes in the inter-object relation rel
		 * @param rel: a relational attribute (object-valued attribute)
		 * @param encodingSchema: WIDE or NARRAW
		 * @param encodingstruct: Lattice (attributesContext.getLattice()), GSH, ConceptImp family
		 * @return binary context which represents the relational extension along rel
		 */
	public static MatrixBinaryRelationBuilder getRelationalscale(MatrixBinaryRelationBuilder objectsContext, 
	MatrixBinaryRelationBuilder attributesContext, InterObjectBinaryRelation rel, Vector encodingstruct, int encodingSchema){
		// 'attributesContext' lattice should be used to encode relation attribute 'InterObjectRelation'
		// and the context 'objectsContext' must be completed		
		Vector scalingConcepts = new Vector(); 
		List<FormalObject> foSet=objectsContext.getObjects();
		// the following loop compute the scaling concepts from the encoding lattticegraph
		for(int k=0;k<encodingstruct.size();k++){
			ConceptNode latticeNode=(ConceptNode) encodingstruct.elementAt(k);
			for(int i=0; i<foSet.size();i++){
				 	Intent targetObjects=getTargetObjects(rel,(FormalObject)foSet.get(i));
				 	// As the objects in targetObjects are InterObjectBinaryRelationAttribute
				 	// they are switched to FormalObject type to enable Extent operation such as intersection				 	
					Extent newExtent = new SetExtent();
					Iterator objectsIt=targetObjects.iterator();
					while(objectsIt.hasNext()){
						InterObjectBinaryRelationAttribute ioba=(InterObjectBinaryRelationAttribute)objectsIt.next();
						String objectName=ioba.toString();
						FormalObject fo=attributesContext.getObjectForName(objectName);
						if(fo!=null) newExtent.add(fo);
					}					
					if(contains(latticeNode,newExtent,encodingSchema)){
						if(!scalingConcepts.contains(latticeNode)) 
							scalingConcepts.add(latticeNode);
						break;
					}
			}//internal for
		}//external for
		// for test only removeIdenticalConcepts(scalingConcepts);
		// creation of the relational extention as a binary relation 
		MatrixBinaryRelationBuilder relExtension = new MatrixBinaryRelationBuilder(foSet.size(),scalingConcepts.size());
		relExtension.setName(rel.getName()+getRSCNameSuffix());
		// replacing formal objects of the relational scale context
		for(int i=0; i<foSet.size();i++){
			FormalObject fo=(FormalObject)foSet.get(i);
			FormalObject newScaleObject=new DefaultFormalObject(fo.getName());
			try {
				relExtension.replaceObject(i,newScaleObject);
			} catch (BadInputDataException e) {
				System.out.println("Scale object not found...");
				e.printStackTrace();
			}
		}
			// replacing formal attribute of the relational scale context
			//String ctxStem= new String("-"+attributesContext.getRelationName());
			String ctxStem="";
			String ovaStem=rel.getName().substring(0,rel.getName().length());
			for(int i=0; i<scalingConcepts.size();i++){
				ConceptNode concept = (ConceptNode) scalingConcepts.elementAt(i);
				// compose relational attribute name
				FormalAttribute newScaleConcept=new DefaultFormalAttribute(ovaStem+ctxStem+":c"+concept.getId().toString());
				try {
					relExtension.replaceAttribute(i,newScaleConcept);
				} catch (BadInputDataException e) {
					System.out.println("Scale attribute not found...");
					e.printStackTrace();
				}
			}		
		// fill in the created relation
		for(int i=0; i<relExtension.getObjectsNumber();i++){
			FormalObject fo = null;
			fo = relExtension.getFormalObject(i);
			for(int j=0; j<scalingConcepts.size();j++){
				 ConceptNode node=(ConceptNode) scalingConcepts.elementAt(j);
				 Extent extent=node.getContent().getExtent();
				 Iterator extIt=extent.iterator();
				 while(extIt.hasNext()) {
				 	FormalObject obj=(FormalObject) extIt.next();
					AbstractFormalAttributeValue value=rel.getRelation(fo,rel.getAttributeForName(obj.toString()));
					if(!value.isFalse()){ 
					FormalAttribute fsa = relExtension.getAttributeForName(ovaStem+ctxStem+":c"+node.getId().toString());
					try {
                        relExtension.setRelation(fo,fsa,FormalAttributeValue.TRUE);
                    } catch (BadInputDataException e) {
                        e.printStackTrace();
                        throw new IndexOutOfBoundsException(e.getMessage());
                    }
					}
				 }//while
			}//internal for
		}//external for
		return relExtension;
	}
	
	/**
	 * @param object0
	 * @return
	 */
	private static Intent getTargetObjects(InterObjectBinaryRelation rel, FormalObject fo) {
		Intent res = new SetIntent(); 
		if(rel.contains(fo)){
			Intent intent=rel.getIntent(fo); 
			res.addAll(intent);
		}
		return res;
	}
	
	private static boolean contains(ConceptNode latticeNode, Extent targetObjects, int encoding){
		if(targetObjects.size()==0) return false;
		Extent nodeExt=latticeNode.getContent().getExtent();
		if(encoding==NARROW_ENCODING)
			if(nodeExt.containsAll(targetObjects)) return true;
			else return false;
		if(encoding==WIDE_ENCODING)
			if(nodeExt.extentIntersection(targetObjects).isEmpty()) return false;
			else return true;
		return false;
	}
	
	public static int getNarrowEncoding(){
		return NARROW_ENCODING;
	}
	
	public static int getWideEncoding(){
			return WIDE_ENCODING;
		}
		
	public static String getRSCNameSuffix(){
			return relScaleCtxNameSuffix;
		}
	private static void removeIdenticalConcepts(Vector concepts){
		for(int i=0; i<concepts.size()-1;i++){
			ConceptNode externalConcept=(ConceptNode) concepts.elementAt(i);
			for(int j=i+1; j<concepts.size();j++){
				ConceptNode internalConcept=(ConceptNode) concepts.elementAt(j);
				if(internalConcept==externalConcept) concepts.remove(j);
			}
		}
		}
}//class