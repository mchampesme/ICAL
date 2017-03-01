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
 * Created on 2004-11-30
 * Author rouanehm (Amine Med ROUANE HACENE)
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package lattice.io;

import java.io.IOException;
import java.io.Writer;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Date;
import java.util.Iterator;
import java.util.Vector;

import lattice.algorithm.rca.RelationalAttributeData;
import lattice.algorithm.rca.RelationalLattice;
import lattice.gui.RelationalContextEditor;
import lattice.util.concept.Concept;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.Node;

public class KrssWriter extends AbstractWriter {
    
	RelationalContextFamily rcf;
	Vector roleNames;
	/**
	 * @param w
	 */
	public KrssWriter(Writer w) {
		super(w);
		roleNames = new Vector(0);
	}

	public void writeRacerkb(RelationalContextFamily rcf) throws IOException {	 	 		
		this.rcf=rcf;			
		//getStream().write(";;; Galicia RCF export \n");
	    //define the header of racer kb definition
		
		String header=defineHeader();
		System.out.println(header);
		getStream().write(header.toString());
		
		// define the signature for a knowledge base. (primitives concepts and roles)
	    String signature=defineKBSignature();
	    System.out.println(signature);
		getStream().write(signature.toString());	    	    

		// define dl-concepts
		//getStream().write(";;; the concepts\n");
		String tbox=defineTBox();
		System.out.println(tbox);
	    getStream().write(tbox.toString());
	    	 	    
	    // define abox
	    String abox=defineABox();
	    System.out.println(abox);
	    getStream().write(abox.toString());
	    
	    // define role assertions
	    String roleAsserts=defineRoleAssertions();
	    System.out.println(roleAsserts);
	    getStream().write(roleAsserts.toString());
	    	    
	    // finalizing export
	    //getStream().write("\n;;; export done \n");
	    Date today = Calendar.getInstance().getTime();	    
	    DateFormat longDateFormatter= SimpleDateFormat.getDateInstance(SimpleDateFormat.LONG);
	    String dateAsText = longDateFormatter.format(today); 
	    //getStream().write(";;; "+dateAsText);	    
	    getStream().close();
	}

	private String defineHeader() {		
		//String header="(in-knowledge-base " + "rcf" + " :init nil)\n";
		String header="(in-knowledge-base " + "RCF" + ")\n";	    
		return header;
	}

	private String defineKBSignature() {	
	    // 
		String kbSignature="(signature \n";
		kbSignature=kbSignature+"           :atomic-concepts(";
		
		// define primitive concepts
		kbSignature=kbSignature+definePrimitiveConcepts();
		
		// define atomic concepts
		kbSignature=kbSignature+defineAtomicConcepts();
		// define role names
		kbSignature=kbSignature+defineRoleNames();
		
		// define individuals
		kbSignature=kbSignature+defineIndividuals();
		
		return kbSignature+"\n)";
	}

	private String definePrimitiveConcepts(){
		// context name is considered as primitive dl-concept
		// formal attributes are also primitive dl-concepts
		String primitiveConcepts="";
		for(int i=0;i<rcf.size();i++) {
			RelationBuilder ctx = rcf.get(i);
			
			// reduced labeling can be obtained this way 			 
			RelationalLattice.removeRedundantLinks(rcf,ctx,RelationalLattice.REDUCED_INTENT);			 
			
			primitiveConcepts=primitiveConcepts+"\n                              "+ctx.getName().toString();
			FormalAttribute[] faSet = ctx.getFormalAttributes();
			for(int j=0;j<faSet.length;j++) {
				if(!RelationalLattice.relationalAttribute(faSet[j]))
					primitiveConcepts=primitiveConcepts+"\n                              "+
					//ctx.getRelationName().toString()+"-"+
					removeWhiteSpaces(faSet[j].toString());
			}
		}
		//primitiveConcepts=primitiveConcepts+")\n";
		return primitiveConcepts;
	}

	private String defineAtomicConcepts(){
		String atomicConcepts="";
		for(int i=0;i<rcf.size();i++) {
			RelationBuilder ctx = rcf.get(i);
			Vector processed=new Vector();
			Vector conceptNodes = new Vector();
			conceptNodes.add(ctx.getLattice().getTop());
			if(!ctx.getLattice().getTop().getContent().getIntent().isEmpty())
				atomicConcepts=atomicConcepts+
				"\n                              "+
				getDlConceptName(ctx.getName(),ctx.getLattice().getTop());
			replaceWithChildren(conceptNodes,ctx.getLattice().getTop());	
			while(conceptNodes.size()>0) {
				// process the first f-concept in the vector
				ConceptNode conceptNode = (ConceptNode) conceptNodes.elementAt(0);
				if(!processed.contains(conceptNode))
					{
						processed.add(conceptNode);
						atomicConcepts=atomicConcepts+
						"\n                              "+
						getDlConceptName(ctx.getName(),conceptNode);	
						replaceWithChildren(conceptNodes,conceptNode);
					}
				else conceptNodes.remove(0);
			}//while
		}//for
		atomicConcepts=atomicConcepts+")\n";
		return atomicConcepts;
	}
		
	private String defineRoleNames(){
		String roles="           :roles( ";
		for(int i=0;i<rcf.size();i++)
			findRoleNames(rcf.get(i));
		for(int i=0;i<roleNames.size();i++)
			roles=roles+"\n                              ( "+
				roleNames.elementAt(i).toString()+" )";
		roles=roles+")\n";
		return roles;		
	}
	
	private String defineIndividuals() {
		String individuals ="           :individuals(";
		for(int i=0;i<rcf.size();i++){
			RelationBuilder ctx = rcf.get(i);
			FormalObject[] foSet = ctx.getFormalObjects();
			for(int j=0;j<foSet.length;j++) 
				individuals=individuals+" "+foSet[j].getName();
		}
		return individuals+")";
	}
		
	/**
	 * @return
	 */
	private String defineTBox() {
		String tbox="\n";
		for(int i=0;i<rcf.size();i++){
			RelationBuilder ctx = rcf.get(i);
			tbox=tbox+defineContextTBox(ctx);
		}
		return tbox;
	}

	/**
	 * @param ctx
	 * @return
	 */
	private String defineContextTBox(RelationBuilder ctx) {
		String tbox="\n";
		// to avoid the multiple processing of concepts 
		Vector processed=new Vector();
		// to let the raisoner client (RICE) to display the context name primitive concept 
		tbox=tbox+"(implies "+ctx.getName()+" "+ctx.getName()+")";
		Vector conceptNodes = new Vector();
		conceptNodes.add(ctx.getLattice().getTop());
		while(conceptNodes.size()>0) {
			// process the first f-concept in the vector
			ConceptNode conceptNode = (ConceptNode) conceptNodes.elementAt(0);
			if(!processed.contains(conceptNode))
				{
					processed.add(conceptNode);
					tbox=tbox+getDLFormulae(ctx,conceptNode);	
					replaceWithChildren(conceptNodes,conceptNode);
				}
			else conceptNodes.remove(0);
		}
		return tbox;
	}

	/**
	 * @param conceptNodes
	 */
	private String getDLFormulae(RelationBuilder context,ConceptNode conceptNode) {
		
		String dlFormulae="\n(implies "+getDlConceptName(context.getName(),conceptNode)+" ";
		Vector subFormulaSet = new Vector();
		
		Concept concept = conceptNode.getContent();
		Intent intent= concept.getIntent(); //.getIntent();
		if(intent.isEmpty()) 
			if(conceptNode==context.getLattice().getTop()) 
				return "";
		Iterator it=intent.iterator();
		while(it.hasNext()) {
			FormalAttribute fa=(FormalAttribute) it.next();
			if(RelationalLattice.relationalAttribute(fa))
				subFormulaSet.add(convertRelAttr2ValueRestriction(fa));
			else
				subFormulaSet.add(removeWhiteSpaces(fa.getName()));
			
		}//while
		
		// add super concepts
		addSuperConcepts(context,conceptNode,subFormulaSet);
		if(subFormulaSet.size()==0){
			System.out.println("Can not find concept parents in the lattice...");
			return "";
		}
		// constructing wff		
		if(subFormulaSet.size()==1) return dlFormulae+ subFormulaSet.elementAt(0).toString()+")\n";
		for(int i=subFormulaSet.size()-1;i>0;i--){
			String wff="( and "+subFormulaSet.elementAt(i-1).toString()+" "+subFormulaSet.elementAt(i).toString()+")";
			subFormulaSet.setElementAt(wff,i-1);
		}
		
		dlFormulae=dlFormulae+ subFormulaSet.elementAt(0).toString()+")";
		return dlFormulae;
	}

	/**
	 * @param subFormulaSet
	 */
	private void addSuperConcepts(RelationBuilder context, ConceptNode conceptNode,Vector subFormulaSet) {
		Iterator it=conceptNode.getParents().iterator();		
		while(it.hasNext()) {
			ConceptNode parent=(ConceptNode)it.next();
			if(!parent.getContent().getIntent().isEmpty())
				// old condition context.getLattice().getTopConceptNode())
				subFormulaSet.add(getDlConceptName(context.getName(),parent));
			} 
	}

	/**
	 * @param name
	 * @return
	 */
	private String getDlConceptName(String ContextName,Node<Concept> name) {
		
		return ContextName+"-C"+name.getId().toString();
	}

	/**
	 * @param fa
	 * @return
	 */
	private String convertRelAttr2ValueRestriction(FormalAttribute rfa) {
		RelationalAttributeData data = RelationalLattice.getRelAttrData(rcf,rfa);		
		return "(all "+data.getRelationName()+" "+data.getContextName()+"-C"+data.getConceptNode().getId().toString()+")";
	}

	/**
	 * @return
	 */
	private String defineABox() {		
		String abox="\n";
		for(int i=0;i<rcf.size();i++) {
			RelationBuilder ctx = rcf.get(i);
			FormalObject[] foSet = ctx.getFormalObjects();
			for(int j=0;j<foSet.length;j++) {
				abox=abox+"\n(instance "+
					removeWhiteSpaces(foSet[j].toString())+ 
					" "+ctx.getName().toString()+")";
			}
		}		 
		return abox;		 
	}

	/**
	 * @return
	 */
	private String defineRoleAssertions() {
		String roleAsserts="\n";
		for(int i=0;i<roleNames.size();i++){
			String roleName = roleNames.elementAt(i).toString();
			RelationBuilder iobr=RelationalContextEditor.getRCF().getForName(roleName);
			if(iobr instanceof InterObjectBinaryRelation){
				roleAsserts=roleAsserts+getRoleAssertions((InterObjectBinaryRelation)iobr,roleName);
			}
		}
		return roleAsserts;		 
	}		 

	private String getRoleAssertions(InterObjectBinaryRelation iobr, String roleName) {
		String roleAsserts="";
		for(int i=0;i<iobr.getObjectsNumber();i++)
			for(int j=0;j<iobr.getAttributesNumber();j++){
				if(iobr.getRelation(i,j).toString().equals("X"))
						roleAsserts=roleAsserts+"\n(related "+iobr.getFormalObject(i)+" "+iobr.getFormalAttribute(j)+ " "+roleName+")";
			}
		return roleAsserts;
	}	
	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		try{
			writeRacerkb((RelationalContextFamily)data);
		}catch(Exception e){
			if(jobObserv!=null) {
				jobObserv.sendMessage(e.getMessage());
				jobObserv.jobEnd(false);
			}
			return;
		}
		if(jobObserv!=null) jobObserv.jobEnd(true);
	}
		
	private void findRoleNames(RelationBuilder context){
		Vector conceptNodes = new Vector();
		conceptNodes.add(context.getLattice().getTop());
		while(conceptNodes.size()>0) checkRoleNames(conceptNodes);			
	}
	/**
	 * @param conceptNodes
	 * @param rcf
	 */
	private void checkRoleNames(Vector conceptNodes) {
//		 pick up the first concept in the list
		ConceptNode conceptNode = (ConceptNode) conceptNodes.elementAt(0); 
		Concept concept = conceptNode.getContent(); 
		// the following condition usually matchs the top concept
		String roleName;
		Intent intent=concept.getIntent();
		Vector conceptLinks=RelationalLattice.getConceptLinks(intent);
		for(int i=0; i<conceptLinks.size();i++) {
			FormalAttribute fa=(FormalAttribute) conceptLinks.elementAt(i);
			RelationalAttributeData relData=RelationalLattice.getRelAttrData(RelationalContextEditor.getRCF(),fa);
			if(!roleNames.contains(relData.getRelationName())) roleNames.add(relData.getRelationName());
		}
		// updating the list of concept nodes
		replaceWithChildren(conceptNodes,conceptNode);				
	}
	
	/**
	 * @param conceptNodes
	 * @param name
	 */
	private void replaceWithChildren(Vector conceptNodes, Node<Concept> name) {
		// remove the already processed concept node from the head of the list
		conceptNodes.remove(0);
		// and adding its children to the tail of the list
		if(name.getChildren().size()>0) {
			Iterator it = name.getChildren().iterator();
			while(it.hasNext()) 
			{
				ConceptNode node= (ConceptNode )it.next();
				if(!conceptNodes.contains(node)) conceptNodes.add(node);
			}
		}
	}

	public static StringBuffer removeWhiteSpaces(String str) {
		StringBuffer buffer = new StringBuffer(str);
		for(int i=0;i<buffer.length();i++)
			if(buffer.charAt(i)==' ') buffer.replace(i,i+1,"");
		return buffer;
	}

	
} //class