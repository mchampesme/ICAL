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
 * Created on 2003-05-08
 *
 * To change this generated comment go to 
 * Window>Preferences>Java>Code Generation>Code and Comments
 */

package lattice.algorithm;
import java.util.Collection;import java.util.Date;import java.util.Hashtable;import java.util.Iterator;import java.util.List;import java.util.TreeMap;import java.util.Vector;import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;import lattice.util.concept.Extent;import lattice.util.concept.FormalAttribute;import lattice.util.concept.Intent;import lattice.util.concept.SetExtent;import lattice.util.concept.SetIntent;import lattice.util.relation.MatrixBinaryRelationBuilder;import lattice.util.structure.ConceptNode;import lattice.util.structure.ConceptNodeImp;
import lattice.util.structure.Node;

/**
 * @author zuojin
 *
 * To change this generated comment go to 
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ValtchevEtAl extends LatticeAlgorithm {
	
	
	
//	private LinkedList allConcepts;
	
	private Vector col;
	public  ValtchevEtAl (MatrixBinaryRelationBuilder br) {
		super(br);
		Date date=new Date();
		System.out.println("Begin Construct ini concept from "+ date.toString());		
		col=(Vector)br.getInitialObjectPreConcept(MatrixBinaryRelationBuilder.NO_SORT);
		date=new Date();
		System.out.println("End Construct ini concept at "+ date.toString());		
		
		if(!col.isEmpty()){
			date=new Date();
			System.out.println("Begin initialization at "+ date.toString());
			iniLattice(col,br);		
			date =new Date();
			System.out.println("End initialization at "+ date.toString());
			
		}
	}


	public void doAlgorithm(){
		jobObserv.sendMessage("Algorithm in progress!\n");
		//doIncre(getBinaryRelation().getInitialObjectPreConcept(MatrixBinaryRelationBuilder.NO_SORT));
		doIncre(col);
//		jobObserv.jobEnd(true);	
	}


	public String getDescription(){
		return "Valtchev et al. incremental lattice update";
	}
	
	public void doIncre(Vector col){
		int size=col.size();
		int j=1;
		Date date=new Date();
		System.out.println("Add the first object at "+date.toString()+"\n");
		for(int i=0;i<size;i++){
			if (i==j*100){
				System.out.println("Add the "+i+"th object"+" at ");
				j++;
				date=new Date();
				System.out.println(date.toString()+"\n");							
			}
			addObject((ConceptImp)col.get(i));
		}
		date=new Date();
		System.out.println("Finish the algorithm at "+date.toString());
	}
	
	
	private void iniLattice(Vector col,MatrixBinaryRelationBuilder br){		ConceptNodeImp.resetNodeId();
		ConceptNode topNode= new ConceptNodeImp((ConceptImp)col.get(0));
		getLattice().setTop(topNode);
		getLattice().incNbOfNodes();
		getLattice().initialiseIntentLevelIndex(br.getAttributesNumber()+1);
		
		int sizeIntent=(((ConceptImp)col.get(0)).getIntent()).size();
		int size=br.getAttributesNumber();
		if(size>sizeIntent){
			ConceptImp bottom=null;
			Intent bottomIntent=new SetIntent();
			Extent bottomExtent=new SetExtent();
			FormalAttribute[] fa=br.getFormalAttributes();
			for(int i=0;i<size;i++){
				bottomIntent.add(fa[i]);
			}
			bottom=new ConceptImp(bottomExtent,bottomIntent);
			ConceptNode bottomNode=new ConceptNodeImp(bottom);			
			getLattice().setUpperCover(topNode,bottomNode);
			getLattice().incNbOfNodes();
		}
		col.remove(0);
	}
	
	private Iterator preProcess(){
		TreeMap sliceLattice =new TreeMap();
		Iterator allConcepts;
		Vector candidate=new  Vector();
		Hashtable dealedConcept=new Hashtable();
		
		
		Node<Concept> topNode=getLattice().getTop();
		candidate.add(topNode);
		while(!candidate.isEmpty()){
			ConceptNode cand=(ConceptNode)candidate.get(0);
			if (dealedConcept.get(cand)!=null) {
				candidate.remove(0);
				continue;
			}
			Integer intentLen=new Integer(((cand.getContent()).getIntent()).size());
			Vector intentNode=new Vector();
			if((intentNode=(Vector)sliceLattice.get(intentLen))!=null){
				intentNode.add(cand);
			}
			else{
				intentNode=new Vector();
				intentNode.add(cand);
				sliceLattice.put(intentLen,intentNode);
			}
			dealedConcept.put(cand,"");
			List children=cand.getChildren();
			candidate.addAll(children);
			candidate.remove(0);			
		}
		allConcepts=((Collection)sliceLattice.values()).iterator();
		return allConcepts;
		
	}


	private void addObject(ConceptImp newConcept){
		Vector allConcepts=new Vector();
		Hashtable modifier=new Hashtable();
		Hashtable chiPlus =new Hashtable();
		Iterator iterNode=preProcess();
		
		while (iterNode.hasNext()){
			Vector intentNode =(Vector)iterNode.next();
			int nodeSize=intentNode.size();
			for(int j=0;j<nodeSize;j++){
				ConceptNode firstNode=(ConceptNode)intentNode.get(j);
				ConceptImp firstConcept =(ConceptImp) firstNode.getContent();
				Vector upp=uppCover(firstNode);
//				System.out.println(upp.toString()+" this is the upp");
				ConceptNode newMaxNodeTemp=argMax(upp,newConcept);

				ConceptNode newMaxNode=null;
				if(newMaxNodeTemp!=null){
//					System.out.println((newMaxNodeTemp.getConcept()).toString()+" the newMaxNodeTemp");	
					newMaxNode=(ConceptNode)chiPlus.get(newMaxNodeTemp);
//					System.out.println((newMaxNode.getConcept()).toString()+" get from chiplus");
				}
				int lengC,lengNew;
				if (newMaxNode==null) {
					lengNew=-1;
				}
				else{
					ConceptImp newMaxConcept=(ConceptImp) newMaxNode.getContent();			
					lengNew=funcQ(newMaxConcept,newConcept).size();
//					System.out.println((newMaxNode.getConcept()).toString()+" "+newConcept.toString());
				}
				lengC=funcQ(firstConcept,newConcept).size();
//				System.out.println(lengNew+" "+lengC);
				if(lengC!=lengNew){
					if(lengC==(firstConcept.getIntent()).size()){										
						Extent extentC=firstConcept.getExtent();
						extentC=extentC.extentUnion(newConcept.getExtent());
//						System.out.println(firstConcept.toString()+" a modifier");
						firstConcept.setExtent(extentC);
						((ConceptNodeImp)firstNode).concept=firstConcept;
						modifier.put(extentC,firstNode);
						newMaxNode=firstNode;
					}
					else{
//						System.out.println(firstConcept.toString()+" a generator");
						Extent extGenC=(Extent)((firstConcept.getExtent()).extentUnion(newConcept.getExtent())).clone();
						ConceptImp genC=new ConceptImp(extGenC,(Intent)funcQ(firstConcept,newConcept).clone());
						ConceptNode genNode=new ConceptNodeImp(genC);
						
						for(int n=0;n<upp.size();n++){
//							System.out.println((((Node)upp.get(n)).getConcept()).toString()+" the "+n+" th concept in upp");
						}
								
						Vector minClo=minClosed(genC,minCandidate(upp,chiPlus));
//						System.out.println(upp.toString());
						int size=minClo.size();
						for(int i=0;i<size;i++){
							ConceptNode coverNode=(ConceptNode)minClo.get(i);
							newLink(coverNode,genNode);
//							System.out.println((coverNode.getConcept()).toString()+" "+genC.toString()+" new link");
							if(modifier.get((coverNode.getContent()).getExtent())!=null){
								dropLink(coverNode,firstNode);
							}
						}
						newLink(genNode,firstNode);
						if(firstNode==getLattice().getTop()){
							getLattice().setTop(genNode);
						}
						newMaxNode=genNode;
						getLattice().add(genNode);
						getLattice().incNbOfNodes();					
					}
//				chiPlus.put(firstNode,newMaxNode);
				}
				chiPlus.put(firstNode,newMaxNode);
			}			
		}
	}



	
	public Vector uppCover(ConceptNode node){
		Vector upp=new Vector();
		upp.addAll(node.getParents());
		
		return upp;
		
	}
	
	public ConceptNode argMax(Vector upp,ConceptImp newConcept){
		ConceptNode max=null;
//		Vector upp=uppCover(node);
		if(upp.isEmpty()) return max;
		int intentLength=funcQ((ConceptImp) ((ConceptNode)upp.get(0)).getContent(),newConcept).size();
		max=(ConceptNode)upp.get(0);
		int size=upp.size();
		for(int i=1;i<size;i++){
			int uppLength=funcQ((ConceptImp) ((ConceptNode)upp.get(i)).getContent(),newConcept).size();
			if(uppLength>intentLength){
				intentLength=uppLength;
				max=(ConceptNode)upp.get(i);
			}
		}
		return max;
	}


	public Intent funcQ(ConceptImp firstConcept, ConceptImp newConcept){
//		int intentLen=0;
		
		Intent cBar=(firstConcept.getIntent()).intentIntersection(newConcept.getIntent());
//		intentLen=cBar.size();
		
		return cBar;
		
	}


	public Vector minCandidate(Vector upp,Hashtable chiPlus){
		Vector candidate=new Vector();
		TreeMap sliceCand=new TreeMap();
		int size=upp.size();
		for(int i=0;i<size;i++){
			ConceptNode node=(ConceptNode)chiPlus.get((ConceptNode)upp.get(i));
			if (node!=null){
				Integer intentLen=new Integer(((node.getContent().getExtent()).size()));
				Vector sortCand=new Vector();
				if((sortCand=(Vector)sliceCand.get(intentLen))!=null){
					sortCand.add(node);
				}
				else{
					sortCand=new Vector();
					sortCand.add(node);
					sliceCand.put(intentLen,sortCand);
				}
//				System.out.println("candidate add "+(node.getConcept()).toString());
//				candidate.add(node);
			}
		}
		Iterator allCand=((Collection)sliceCand.values()).iterator();
		while(allCand.hasNext()){
			Vector sortCand=(Vector)allCand.next();
			int nodeSize=sortCand.size();
			for(int j=0;j<nodeSize;j++){
				candidate.add((ConceptNode)sortCand.get(j));
			}
		}
		return candidate;		
	}
	
	public Vector minClosed(ConceptImp first, Vector candidate){
		Vector minClo=new Vector();
		Extent firstExtent =first.getExtent();
		Extent face=(Extent)(firstExtent.clone());
		int size =candidate.size();
		for(int i=0;i<size;i++){
			ConceptImp conCBar=(ConceptImp) ((ConceptNode)candidate.get(i)).getContent();
			Extent extCBar=conCBar.getExtent();
			if ((firstExtent.toString()).equals((face.extentIntersection(extCBar)).toString())){
				minClo.add((ConceptNode)(candidate.get(i)));
				face=face.extentUnion(extCBar);				
			}			
		}
		
		return minClo;
		
	}
	
	public void newLink(ConceptNode node,ConceptNode childNode){
		getLattice().setUpperCover(node,childNode);
	}
	
	public void dropLink(ConceptNode node,ConceptNode childNode){
		childNode.removeParent(node);
		node.removeChild(childNode);
	}
}
