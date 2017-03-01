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
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package lattice.algorithm.rca;

import java.util.Collection;
import java.util.Comparator;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.TreeMap;
import java.util.Vector;

import lattice.util.Equivalence;
import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalAttributeValue;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
import lattice.util.structure.Node;

/**
 * @author rouanehm
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */

public class AttributeLatticeUpdate {  
   
  public AttributeLatticeUpdate() {}
  
  public String getDescription() {
	 return "Online attribute lattice update";
   }

  private static Iterator preProcess(CompleteConceptLattice lattice) {
	TreeMap sliceLattice = new TreeMap();
	Iterator allConcepts;
	Vector candidate = new Vector();
	Hashtable dealedConcept = new Hashtable();

	Node<Concept> topNode = lattice.getTop();
	candidate.add(topNode);
	while (!candidate.isEmpty()) {
	  ConceptNode cand = (ConceptNode) candidate.get(0);
	  if (dealedConcept.get(cand) != null) {
		candidate.remove(0);
		continue;
	  }

	  Integer IntentLen = new Integer( ( (cand.getContent()).getIntent()).size());
	  Vector IntentNode = new Vector();
	  if ( (IntentNode = (Vector) sliceLattice.get(IntentLen)) != null) {
		IntentNode.add(cand);

	  }
	  else {
		IntentNode = new Vector();
		IntentNode.add(cand);
		sliceLattice.put(IntentLen, IntentNode);

	  }
	  dealedConcept.put(cand, "");
	  List children = cand.getChildren();
	  candidate.addAll(children);
	  candidate.remove(0);
	}
	allConcepts = ( (Collection) sliceLattice.values()).iterator();

	return allConcepts;
  }

  public  static Vector addAttribute(MatrixBinaryRelationBuilder ctx, FormalAttribute fa, Extent faImage) {  	
  	ctx.addAttribute(fa);
 	Iterator objects=faImage.iterator();
 	while(objects.hasNext()){
 		FormalObject fo=(FormalObject) objects.next();
 		try {
            ctx.setRelation(fo,fa,FormalAttributeValue.TRUE);
        } catch (BadInputDataException e) {
            e.printStackTrace();
            throw new IndexOutOfBoundsException(e.getMessage());
        }
 	} 	
	// to be added to a context, a concept is created 
	// made from the attribute and its corresponding objects 
	Intent intent = new SetIntent();
	intent.add(fa);
	ConceptImp attrConcept=new ConceptImp(faImage,intent);  	
	return addAttribute(ctx.getLattice(),attrConcept);  	
  }

  public  static Vector addAttribute(CompleteConceptLattice lattice, ConceptImp newConcept) {

	ConceptNodeImp.setNodeId(lattice.size());
	Vector newConcepts = new Vector();
	Hashtable modified = new Hashtable();
	
	Extent e = new SetExtent();
	Hashtable table = new Hashtable();
	Node<Concept> minimal;

	TreeMap vSort = new TreeMap();

	Hashtable chiPlus = new Hashtable();
	Vector lower = new Vector();

	modified.clear();

	Iterator iterNode = preProcess(lattice);

	while (iterNode.hasNext()) {
	  Vector ExtentNode = (Vector) iterNode.next();
	  int nodeSize = ExtentNode.size();
  
	  for (int j = 0; j < nodeSize; j++) {
		ConceptNode firstNode = (ConceptNode) ExtentNode.get(j);
		ConceptImp firstConcept = (ConceptImp) firstNode.getContent();

		e = firstConcept.getExtent().extentIntersection(newConcept.getExtent());
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
       
			modified.put(intentC, firstNode);
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

	Iterator itGen = ( (Collection) vSort.values()).iterator();
	while (itGen.hasNext()) {
	  Hashtable th = (Hashtable) itGen.next();
	  Enumeration e1 = (Enumeration) th.keys();
      
	  while (e1.hasMoreElements()) {
		Extent extent = (Extent) e1.nextElement();
		Equivalence equival = (Equivalence) th.get(extent);
		ConceptNode nodeMin = (ConceptNode) equival.getMinimal();

		Intent IntGenC = nodeMin.getContent().getIntent().intentUnion(newConcept.
			getIntent());
		ConceptImp genC = new ConceptImp(extent, IntGenC);
		ConceptNode genNode = new ConceptNodeImp(genC);
	   lattice.add(genNode);
        
		newConcepts.add(genNode);
		lower = lowerCover(nodeMin);

		Vector minClo = minClosed(genC, minCandidate(lower, chiPlus));
		int size = minClo.size();

		for (int i = 0; i < size; i++) {
		  ConceptNode coverNode = (ConceptNode) minClo.get(i);
		  newLink(lattice,genNode, coverNode);
         

		  if (modified.get( (coverNode.getContent()).getIntent()) != null) {
			dropLink(nodeMin, coverNode);
           
		  }
		}
		newLink(lattice,nodeMin, genNode);

		lattice.add(genNode);
		lattice.incNbOfNodes();
		chiPlus.put(nodeMin, genNode);
	  }
	}
   return newConcepts;
  	
  }

  public static Vector minCandidate(Vector lower, Hashtable chiPlus) {
	Vector candidate = new Vector();
	TreeMap sliceCand = new TreeMap();
	int size = lower.size();
	for (int i = 0; i < size; i++) {
	  ConceptNode node = (ConceptNode) chiPlus.get( (ConceptNode) lower.get(i));

     

	  // instruction ajoutee dernierement pour la mise a jour de l'ordre
	  if (node != null) {
		boolean stop = false;
		ConceptNode node1 = node;
		while (!stop) {
		  node = (ConceptNode) chiPlus.get(node1);
		  //System.out.println(node+" chiPlus: "+node);
		  if ( (node == null) || (node.equals(node1)))
			stop = true;
		  else
			node1 = node;
		}
		node = node1;
	  }
	  //fin instruction

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
		candidate.add( (ConceptNode) sortCand.get(j));
	  }
	}
	return candidate;
  }

  public static Vector minClosed(ConceptImp first, Vector candidate) {
	Vector minClo = new Vector();
	Intent firstIntent = first.getIntent();
	Intent face = (Intent) (firstIntent.clone());
	int size = candidate.size();
	for (int i = 0; i < size; i++) {
	  ConceptImp conCBar = (ConceptImp) ( (ConceptNode) candidate.get(i)).getContent();
	  Intent intCBar = conCBar.getIntent();
	  if ( (firstIntent.toString()).equals( (face.intentIntersection(intCBar)).
										   toString())) {
		minClo.add( (ConceptNode) (candidate.get(i)));
		face = face.intentUnion(intCBar);
	  }
	}

	return minClo;

  }

  public static void newLink(CompleteConceptLattice lattice, ConceptNode node, ConceptNode childNode) {
   lattice.setUpperCover(node, childNode);
  }

  public static void dropLink(ConceptNode node, ConceptNode childNode) {
	childNode.removeParent(node);
	node.removeChild(childNode);
  }

  public static Vector lowerCover(ConceptNode node) {
	Vector lower = new Vector();
	lower.addAll(node.getChildren());

	return lower;

  }
  
 

  static class sizeCompare
	  implements Comparator {

	public int compare(Object o1, Object o2) {
	  Integer i1 = (Integer) o1;
	  Integer i2 = (Integer) o2;
	  return (i2.intValue() - i1.intValue());
	}
  }
  
}
