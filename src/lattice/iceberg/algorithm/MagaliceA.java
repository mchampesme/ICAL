/*
 ***********************************************************************
 * Copyright (C) 2004 The Galicia Team 
 *
 * Modifications to the initial code base are copyright of their
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

package lattice.iceberg.algorithm;

import java.util.*;

import lattice.algorithm.LatticeAlgorithmInc;
import lattice.util.Equivalence;
import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
import lattice.util.structure.Node;




/**
 * @author Kamal Nehme
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */



public class MagaliceA extends LatticeAlgorithmInc {

  private Vector col;
  private int nbrAttrs;
  private int nbrObjs;
  private double minSupp;
  private int nbGens;
 
  private Hashtable modifier = new Hashtable();
  
  private Hashtable newConcepts = new Hashtable();
  
  private Vector vect = new Vector();

  public MagaliceA(MatrixBinaryRelationBuilder br, double minSupp) {
    super(br);
    Date date = new Date();
    
    this.minSupp = minSupp;
    nbrAttrs = br.getAttributesNumber();
    nbrObjs = br.getObjectsNumber();
    col = (Vector) br.getInitialAttributePreConcept(MatrixBinaryRelationBuilder.NO_SORT);
    date = new Date();
    
    if (!col.isEmpty()) {
      date = new Date();
      System.out.println("Begin initialization from " + date.toString());
      iniLattice(col, br);

      date = new Date();
      System.out.println("End initialization at " + date.toString());
    }
  }
  
  public MagaliceA(CompleteConceptLattice l,double minSupp) {
  	this.minSupp = minSupp;
    Date date = new Date();
    System.out.println("Begin initialization from " + date.toString());
    setLattice(l);
	nbrObjs = getLattice().getTop().getContent().getExtent().size();
    
    
    if ( l.getBottom()== null){
    	//System.out.println("No Bottom Node in the Iceberg ");
    }
   
    date = new Date();
    System.out.println("End initialization at " + date.toString());
  }


  public void doAlgorithm() {
    //jobObserv.sendMessage("AttIncre Algorithm is in progress!\n");
    doIncre(col);
    getLattice().setMinSupp(this.minSupp);
  }

  public String getDescription() {
    return "Attribute_Incremental Lattice";
  }

  public void doIncre(Vector col) {
    int size = col.size();
    int j = 1;
    Date date = new Date();
   
    for (int i = 0; i < size; i++) {
      addConcept( (ConceptImp) col.get(i));
    }
    
	Node<Concept> nBottom = getLattice().getBottom();
	if (( nBottom != null) && (nBottom.getContent().getIntent().size() !=  nbrAttrs))
		getLattice().setBottom(null);
    
    date = new Date();
    //System.out.println("Nbr of Concepts: " + getLattice().getSize());
    //System.out.println("Finish the AttIncre algorithm at " + date.toString());
    //System.out.println("lattice bottom: "+getLattice().getBottomConceptNode().getConcept().getIntent().toString());
  }

  private void iniLattice(Vector col, MatrixBinaryRelationBuilder br) {
    getLattice().initialiseIntentLevelIndex(br.getAttributesNumber() + 1);
    Node<Concept> bottomNode = null;
    Extent bottomExt = (Extent) ( (Concept) col.get(0)).getExtent();
    if ( ( (bottomExt.size()) / (double)this.nbrObjs) >= this.minSupp) {
      bottomNode = new ConceptNodeImp( (ConceptImp) col.get(0));
      getLattice().add(bottomNode);
    }
    Node<Concept> topNode = null;
    int sizeExtent = ( ( (Concept) col.get(0)).getExtent()).size();
    int size = br.getObjectsNumber();
    if (size > sizeExtent) {
      ConceptImp top = null;
      Intent topIntent = new SetIntent();
      Extent topExtent = new SetExtent();
      FormalObject[] fa = br.getFormalObjects();
      for (int i = 0; i < size; i++) {
        topExtent.add(fa[i]);
      }
      top = new ConceptImp(topExtent, topIntent);
      topNode = new ConceptNodeImp(top);
      getLattice().add(topNode);
      getLattice().setTop(topNode);
      
      if (bottomNode != null) {
        getLattice().setUpperCover(topNode, bottomNode);
        getLattice().incNbOfNodes();
        getLattice().setBottom(bottomNode);
      }
    }
    else {
      getLattice().setTop(bottomNode);
    }
    col.remove(0);
    getLattice().incNbOfNodes();
    getLattice().initialiseIntentLevelIndex(br.getAttributesNumber() + 1);

  }

  private Iterator preProcess() {
 
    TreeMap sliceLattice = new TreeMap();
    Iterator allConcepts;
    Vector candidate = new Vector();
    Hashtable dealedConcept = new Hashtable();

    Node<Concept> topNode = getLattice().getTop();
    candidate.add(topNode);
    while (!candidate.isEmpty()) {
      Node<Concept> cand = (Node<Concept>) candidate.get(0);
      if (dealedConcept.get(cand) != null) {
        candidate.remove(0);
        continue;
      }

      Integer ExtentLen = new Integer( ( (cand.getContent()).getIntent()).size());
      Vector ExtentNode = new Vector();
      if ( (ExtentNode = (Vector) sliceLattice.get(ExtentLen)) != null) {
        ExtentNode.add(cand);

      }
      else {
        ExtentNode = new Vector();
        ExtentNode.add(cand);
        sliceLattice.put(ExtentLen, ExtentNode);

      }
      dealedConcept.put(cand, "");
      List children = cand.getChildren();
      candidate.addAll(children);
      candidate.remove(0);
    }
    allConcepts = ( (Collection) sliceLattice.values()).iterator();

    return allConcepts;

  }

  public void addConcept(Concept newConcept) {

    Hashtable unfrequent = new Hashtable();
    Extent e = new SetExtent();
    Hashtable table = new Hashtable();
    Node<Concept> minimal;

    TreeMap vSort = new TreeMap();

    Hashtable chiPlus = new Hashtable();
    Vector lower = new Vector();

    modifier.clear();

    Iterator iterNode = preProcess();

    while (iterNode.hasNext()) {
      Vector ExtentNode = (Vector) iterNode.next();
      int nodeSize = ExtentNode.size();
    
      for (int j = 0; j < nodeSize; j++) {
        Node<Concept> firstNode = (Node<Concept>) ExtentNode.get(j);
        Concept firstConcept = firstNode.getContent();

        if (unfrequent.get(firstConcept) == null) {
          e = firstConcept.getExtent().extentIntersection(newConcept.getExtent());


          if (e.size() < minSupp * nbrObjs) {
            Iterator itr = firstNode.getChildren().iterator();
            while (itr.hasNext()) {
              Node<Concept> child = (Node<Concept>) itr.next();
              unfrequent.put(child, "");
            }
          }

          else {
          
            Integer eSize = new Integer(e.size());
            Hashtable ht;
            ht = (Hashtable) vSort.get(eSize);

            if (ht == null)
              ht = new Hashtable();

            Equivalence EqGen = (Equivalence) ht.get(e);

            if (EqGen == null)
              EqGen = new Equivalence(firstNode);

            if (firstConcept.getExtent().size() == e.size()) { // firstConcept is a modidied
              Intent intentC = firstConcept.getIntent().intentUnion(newConcept.
                  getIntent());
              firstConcept.setIntent(intentC);
              
              if (firstNode.getContent().getIntent().size() ==  nbrAttrs)
              	getLattice().setBottom(firstNode);

              modifier.put(intentC, firstNode);
              minimal = EqGen.getMinimal();
              chiPlus.put(minimal, firstNode);
              chiPlus.put(firstNode, firstNode);

              ht.remove(e);
              vSort.put(eSize, ht);
            }

            else {

              Node<Concept> nTemp = EqGen.getMinimal();
              chiPlus.put(nTemp, firstNode);
              EqGen.setMinimal(firstNode);
              ht.put(e, EqGen);
              vSort.put(eSize, ht);
            }
          }
        }
      }
    }

    Iterator itGen = ( (Collection) vSort.values()).iterator();
    while (itGen.hasNext()) {
      Hashtable th = (Hashtable) itGen.next();
      Enumeration e1 = (Enumeration) th.keys();
   
      while (e1.hasMoreElements()) {
        Extent extent = (Extent) e1.nextElement();
        Equivalence equival = (Equivalence) th.get(extent);
        Node<Concept> nodeMin = (Node<Concept>) equival.getMinimal();
		Intent IntGenC = nodeMin.getContent().getIntent().intentUnion(newConcept.
            getIntent());
        ConceptImp genC = new ConceptImp(extent, IntGenC);
        Node<Concept> genNode = new ConceptNodeImp(genC);
        getLattice().add(genNode);
        
        if (genC.getIntent().size() ==  nbrAttrs)
        	getLattice().setBottom(genNode);

        lower = lowerCover(nodeMin);

        Vector minClo = minClosed(genC, minCandidate(lower, chiPlus));
        int size = minClo.size();

        for (int i = 0; i < size; i++) {
          Node<Concept> coverNode = (Node<Concept>) minClo.get(i);
          newLink(genNode, coverNode);
         
          if (modifier.get( (coverNode.getContent()).getIntent()) != null) {
            dropLink(nodeMin, coverNode);
          }
        }
        newLink(nodeMin, genNode);

        getLattice().add(genNode);
        getLattice().incNbOfNodes();
        chiPlus.put(nodeMin, genNode);
      }
    }
  }

  public Vector minCandidate(Vector lower, Hashtable chiPlus) {
    Vector candidate = new Vector();
    TreeMap sliceCand = new TreeMap();
    int size = lower.size();
    for (int i = 0; i < size; i++) {
      Node<Concept> node = (Node<Concept>) chiPlus.get( (Node<Concept>) lower.get(i));

      if (node != null) {
        boolean stop = false;
        Node<Concept> node1 = node;
        while (!stop) {
          node = (Node<Concept>) chiPlus.get(node1);
         
          if ( (node == null) || (node.equals(node1)))
            stop = true;
          else
            node1 = node;
        }
        node = node1;
      }
     

      if (node != null) {
       
        Integer extentLen = new Integer( ( (node.getContent().getIntent()).size()));
        Vector sortCand = new Vector();
        if ( (sortCand = (Vector) sliceCand.get(extentLen)) != null) {
          sortCand.add(node);
        }
        else {
          sortCand = new Vector();
          sortCand.add(node);
          sliceCand.put(extentLen, sortCand);
        }
      }
    }
    Iterator allCand = ( (Collection) sliceCand.values()).iterator();
    while (allCand.hasNext()) {
      Vector sortCand = (Vector) allCand.next();
      int nodeSize = sortCand.size();
      for (int j = 0; j < nodeSize; j++) {
        candidate.add( (Node<Concept>) sortCand.get(j));
      }
    }
    return candidate;
  }

  public Vector minClosed(Concept first, Vector candidate) {
    Vector minClo = new Vector();
    Intent firstIntent = first.getIntent();
    Intent face = (Intent) (firstIntent.clone());
    int size = candidate.size();
    for (int i = 0; i < size; i++) {
      Concept conCBar = ( (Node<Concept>) candidate.get(i)).getContent();
      Intent intCBar = conCBar.getIntent();
      if ( (firstIntent.toString()).equals( (face.intentIntersection(intCBar)).
                                           toString())) {
        minClo.add( (Node<Concept>) (candidate.get(i)));
        face = face.intentUnion(intCBar);
      }
    }

    return minClo;

  }

  public void newLink(Node<Concept> node, Node<Concept> childNode) {
    getLattice().setUpperCover(node,childNode); 
  }

  public void dropLink(Node<Concept> node, Node<Concept> childNode) {
    childNode.removeParent(node);
    node.removeChild(childNode);
  }

  public Vector lowerCover(Node<Concept> node) {
    Vector lower = new Vector();
    lower.addAll(node.getChildren());

    return lower;

  }
  
  public void addAttr(ConceptImp c) {
    addConcept(c);
  }

 

  static class sizeCompare
      implements Comparator {

    public int compare(Object o1, Object o2) {
      Integer i1 = (Integer) o1;
      Integer i2 = (Integer) o2;
      return (i2.intValue() - i1.intValue());
    }
  }

  public void countGens(Node<Concept> nod, Vector visited) {
    nbGens += nod.getContent().getGenerator().size();
    Iterator it = nod.getChildren().iterator();
    while (it.hasNext()) {
      ConceptNodeImp pt = (ConceptNodeImp) it.next();
      if (!visited.contains(pt)) {
        visited.add(pt);
        countGens(pt, visited);
      }
    }
  }
  
  public Node<Concept> conceptAttribute (Node<Concept> node,Extent e,Vector visited){
  	boolean found = false;
  		Node<Concept> result = null;
  		
  		if(node.getContent().getExtent().equals(e)==true){
  			found = true;
  			result = node;
  		}
  		
  		else{
  			Iterator itChild = node.getChildren().iterator();
  			while (itChild.hasNext() && !found){
  				Node<Concept> child = (Node<Concept>) itChild.next();
  				if (!visited.contains(child)) {
        			visited.add(child);
  					result = conceptAttribute(child,e,visited);
  				}
  				if(result!=null) found=true;	
  			}
  		}
  		return(result);
  }
  
  
  public Node<Concept> isNew(Node<Concept> node,Intent intent){
  	Node<Concept> genitor = null;
  	boolean fini = false;
  	
  	Intent inte = (Intent) node.getContent().getIntent().clone();
  	inte.removeAll(intent);
  	
  	Iterator itr = node.getParents().iterator();
  	while ((itr.hasNext())&& (!fini)){
  		Node<Concept> prt = (Node<Concept>) itr.next();
  		if (prt.getContent().getIntent().intentIntersection(intent).equals(intent)==false)
  			if (prt.getContent().getIntent().size()== inte.size()){
  				fini = true;
  				genitor = prt;
  			}	
  	}
  	return (genitor);
  }
  
  private Iterator Sort(Node<Concept> node) {
  
    TreeMap sliceLattice = new TreeMap();
    Iterator allConcepts;
    Vector candidate = new Vector();
    Hashtable dealedConcept = new Hashtable();

    candidate.add(node);
    while (!candidate.isEmpty()) {
      Node<Concept> cand = (Node<Concept>) candidate.get(0);
      if (dealedConcept.get(cand) != null) {
        candidate.remove(0);
        continue;
      }

     
      Integer ExtentLen = new Integer( ( (cand.getContent()).getIntent()).size());
      Vector ExtentNode = new Vector();
      if ( (ExtentNode = (Vector) sliceLattice.get(ExtentLen)) != null) {
        ExtentNode.add(cand);

      }
      else {
        ExtentNode = new Vector();
        ExtentNode.add(cand);
        sliceLattice.put(ExtentLen, ExtentNode);

      }
      dealedConcept.put(cand, "");
      List children = cand.getChildren();
      candidate.addAll(children);
      candidate.remove(0);
    }
    allConcepts = ( (Collection) sliceLattice.values()).iterator();

    return allConcepts;

  }
  
  public void updateOrder(Node<Concept> node, Hashtable table){
  	
  	Node<Concept> newNode = null;
  	Vector oldParents = new Vector();
  	Vector newParents = new Vector();
  	
  	Iterator itrParents = node.getParents().iterator();
  	while (itrParents.hasNext()){
  		Node<Concept> ndParent = (Node<Concept>) itrParents.next();	
  		newNode = (Node<Concept>) table.get(ndParent);
  		if (newNode == null){
  			oldParents.add(ndParent);
  		}
  		else{
  			newParents.add(ndParent);
  		}
  	}
  	
  	
  	while(!newParents.isEmpty()){
  		Node<Concept> ndPrt = (Node<Concept>) newParents.elementAt(0);
  		Node<Concept> nodeGen = (Node<Concept>) table.get(ndPrt);
  		boolean fini = false;
  		Intent intents = new SetIntent();
  		Node<Concept> nd = null;
  		Iterator its = oldParents.iterator();
  		
  		if (its.hasNext()){
  			nd = (Node<Concept>) its.next();
  			intents = nd.getContent().getIntent().intentIntersection(ndPrt.getContent().getIntent());
  			if (nodeGen.getContent().getIntent().equals(intents))
  				fini = true;
  		
  			while ((fini == false) && (its.hasNext())){
  				nd = (Node<Concept>) its.next();
  				intents = nd.getContent().getIntent().intentIntersection(ndPrt.getContent().getIntent());
  				if (nodeGen.getContent().getIntent().equals(intents))
  					fini = true;
  			}
  			if (fini == false){
  				node.getParents().add(nodeGen);
  				nodeGen.getChildren().add(node);
  			}
  		}
  		
  		else{
  			node.getParents().add(nodeGen);
  			nodeGen.getChildren().add(node);
  		}
  		newParents.remove(0);
  	}

  }
  
  public void deleteConcept(Concept c){
	  
	  Node<Concept> na = conceptAttribute(getLattice().getTop(),c.getExtent(),new Vector());
	 System.out.println("Concept_Attribute (a',a'') : #" +na.getId());
	 
	  Iterator itr = Sort(na);
	  Node<Concept> genitor = null;
	  while (itr.hasNext()){
		  Vector ExtentNode = (Vector) itr.next();
		int nodeSize = ExtentNode.size();
		
		for (int s = 0; s < nodeSize; s++) {
		  Node<Concept> firstNode = (Node<Concept>) ExtentNode.get(s);
		  Concept firstConcept = firstNode.getContent();
		  genitor = isNew(firstNode,c.getIntent());
		  if (genitor == null){
			  firstConcept.getIntent().removeAll(c.getIntent());
			  updateOrder(firstNode,newConcepts);
		  }
		  else{
			   newConcepts.put(firstNode,genitor);
			   vect.add(firstNode);
		  }
      
		}
	  }
      	
		while (!vect.isEmpty()){
		  Node<Concept> nS = (Node<Concept>) vect.elementAt(0);
		 
		  Vector vPt = new Vector(nS.getParents());
		  while (!vPt.isEmpty()){
			  Node<Concept> nPt = (Node<Concept>) vPt.elementAt(0);
			  nS.removeParent(nPt);
			  nPt.removeChild(nS);
			  vPt.remove(0);
		  }
      	
 
		  Vector vCh = new Vector(nS.getChildren());
		  while (!vCh.isEmpty()){
			  Node<Concept> nCh = (Node<Concept>) vCh.elementAt(0);
			
			  nCh.removeParent(nS);
			  nS.removeChild(nCh);
			  vCh.remove(0);
		  }
		  
		  vect.remove(0);	
		}
  }

  
}
