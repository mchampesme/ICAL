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




public class MagaliceAGen extends LatticeAlgorithmInc {

	 private Vector col;
	  private int nbrAttrs;
	  private int nbrObjs;
	  private double minSupp;
	  private int nbGens;
	  //private Vector Attrib = new Vector();
	  //private Node BottomFictif ;
	  
	  public String str = "";

	  private Hashtable modifier = new Hashtable();
	  
	  private Hashtable newConcepts = new Hashtable();
	  
	  private Vector vect = new Vector();

	  private Set visited = new HashSet();
	  
	  Extent tempExtent = new SetExtent();

	  public MagaliceAGen(MatrixBinaryRelationBuilder br, double minSupp) {
	    super(br);
	    Date date = new Date();
	    
	    //Attrib = br.getAttributes();
	    System.out.println("Begin Construct ini concept from " + date.toString());

	    this.minSupp = minSupp;
	    nbrAttrs = br.getAttributesNumber();
	    nbrObjs = br.getObjectsNumber();
	    col = (Vector) br.getInitialAttributePreConcept(MatrixBinaryRelationBuilder.NO_SORT);
	    date = new Date();
	    System.out.println("End Construct ini concept at " + date.toString());

	    if (!col.isEmpty()) {
	    	date = new Date();
	        
	        str = str + "MagaliceA \t Begin Execution at: " + date.toString();
	      System.out.println("Begin initialization from " + date.toString());
	      iniLattice(col, br);

	      //System.out.println("Iceberg Top: "+getLattice().getTop());
	      //System.out.println("TOP Generator: "+getLattice().getTop().getConcept().getGenerator());

	      date = new Date();
	      System.out.println("End initialization at " + date.toString());
	      //System.out.println("nbrObjs: "+nbrObjs);
	    }
	  }
	  
	  public MagaliceAGen(CompleteConceptLattice l,double minSupp) {
	  	this.minSupp = minSupp;
	    Date date = new Date();
	    System.out.println("Begin initialization from " + date.toString());
	    setLattice(l);
		nbrObjs = getLattice().getTop().getContent().getExtent().size();
	    
	    
	    if ( l.getBottom()== null){
	    	System.out.println("No Bottom Node in the Iceberg ");
	    }
	   
	    date = new Date();
	    System.out.println("End initialization at " + date.toString());
	  }


	  public void doAlgorithm() {
	    //jobObserv.sendMessage("AttIncre Algorithm is in progress !\n");
	    //doIncre(getBinaryRelation().getInitialObjectPreConcept(MatrixBinaryRelationBuilder.NO_SORT));
	    doIncre(col);
	    getLattice().setMinSupp(this.minSupp);
//			jobObserv.jobEnd(true);
	  }

	  public String getDescription() {
	    return "AttIncre Lattice Algorithm";
	  }

	  public void doIncre(Vector col) {
	    int size = col.size();
	    int j = 1;
	    Date date = new Date();
	    //System.out.println("Add the first attribute at "+date.toString()+"\n");

	    if (getLattice().getBottom() != null) {
	      Vector vect = new Vector();
	      vect.add(getLattice().getBottom().getContent().getIntent());
	      getLattice().getBottom().getContent().setGenerator(vect);
	    }

	    for (int i = 0; i < size; i++) {
	    	
	    	//System.out.println("Add the " + i + "th attribute");
	      /*if (i == j * 100) {
	        System.out.println("Add the " + i + "th attribute" + " at ");
	        j++;
	        date = new Date();
	        System.out.println(date.toString() + "\n");
	      }*/
	      
	      date = new Date();
	      
	     //System.out.println("\n Add Attribute: "+i+"\t at: "+date+"\t #OfConcepts: "+this.getLattice().getSize());
		 
	      //System.out.println();
	     //System.out.println("Add the "+((ConceptImp) col.get(i)).getIntent()+"th attribute");
	      addConcept( (ConceptImp) col.get(i));

	      //visited.clear();
	      //saveIceberg(getLattice().getTop());
	    }
	    
		Node<Concept> nBottom = getLattice().getBottom();
		if (( nBottom != null) && (nBottom.getContent().getIntent().size() !=  nbrAttrs))
			getLattice().setBottom(null);
	    /*
	    Node nBottom = getLattice().getBottom();
	    if (nBottom.getConcept().getIntent().size() ==  nbrAttrs)
	    	System.out.println("Bottom is frequent :"+nBottom.getId());
	    
	    else{
	    	
	    	Extent extBottom = new SetExtent();
	    	Intent intBottom = new SetIntent();
	    	intBottom.addAll(Attrib);
	    	ConceptImp BottomConcept = new ConceptImp(extBottom,intBottom);
	    	BottomFictif = new LatticeNode(BottomConcept);
	    	getLattice().setBottom(BottomFictif);
	    	System.out.println("Bottom is Fictif: "+getLattice().getBottom().getId());
	    }
	   	*/
		
	    //visited.clear();
	    //saveIceberg(lcl.getTop());
	    
		date = new Date();
	    System.out.println("Nbr of Concepts: " + getLattice().size());
	    System.out.println("Finish the AttIncre algorithm at " + date.toString());
	    
	    str = str + "\t End Execution at: " + date.toString()+ "\t Nbr of Concepts: " + getLattice().size();
	    countGens(getLattice().getTop(), new Vector());
	    System.out.println("Nbr of Gens: " + nbGens);
	    
	    
	    
	    System.out.println("Finish the AttIncre algorithm at " + date.toString());
	  }

	  private void iniLattice(Vector col, MatrixBinaryRelationBuilder br) {
	  	ConceptNodeImp.resetNodeId();
	    getLattice().initialiseIntentLevelIndex(br.getAttributesNumber() + 1);
	    List gen = new Vector();
	    Node<Concept> bottomNode = null;
	   // System.out.println("Execution of 1st attribut");
	    Extent bottomExt = (Extent) ( (Concept) col.get(0)).getExtent();
	    if ( ( (bottomExt.size()) / (double)this.nbrObjs) >= this.minSupp) {
	      bottomNode = new ConceptNodeImp( (ConceptImp) col.get(0));
	      getLattice().add(bottomNode);
	      //gen.addAll(bottomNode.getConcept().getIntent());
		  gen.add(bottomNode.getContent().getIntent());
	      bottomNode.getContent().setGenerator(gen);

	      //System.out.println("Node: #"+bottomNode+"... "+bottomNode.getConcept().toString());
	      //System.out.println("GEN: "+gen);
	      //System.out.println("bottomNode: "+bottomNode);
	      //System.out.println("#"+bottomNode +" Generators: "+bottomNode.getConcept().getGenerator());
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
	      gen.clear();
	      if (topNode.getContent().getIntent().size() != 0)
	        gen.add(topNode.getContent().getIntent());
	     // topNode.getConcept().setGenerator(gen);
	      //System.out.println("topNode: "+topNode);
	      if (bottomNode != null) {
	        getLattice().setUpperCover(topNode, bottomNode);
	        getLattice().incNbOfNodes();
	        getLattice().setBottom(bottomNode);
	      }
	    }
	    else {
	      getLattice().setTop(bottomNode);
	    }
	    
	   
	    gen = getLattice().getTop().getContent().getGenerator();
	    if (gen == null) {
	    	gen = new Vector();
	    	gen.add(new SetIntent());
	    }
	    /*else{
	    	gen.insertElementAt(new SetIntent(),0);
	    }*/
	    	
	    getLattice().getTop().getContent().setGenerator(gen);
	    
		//System.out.println(">>> #"+getLattice().getTopConceptNode().getId()+" Generators: "+getLattice().getTopConceptNode().getConcept().getGenerator());
	    
	    col.remove(0);
	    getLattice().incNbOfNodes();
	    getLattice().initialiseIntentLevelIndex(br.getAttributesNumber() + 1);

	  }

	  private Iterator preProcess() {
	    //TreeMap sliceLattice =new TreeMap(new sizeCompare());
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

	      //Integer ExtentLen=new Integer(((cand.getConcept()).getExtent()).size());
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

	    //System.out.println("(a',a): "+newConcept);

	    //Vector generator = new Vector();
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
	      //System.out.println("EXTENT SIZE: "+nodeSize);
	      for (int j = 0; j < nodeSize; j++) {
	        Node<Concept> firstNode = (Node<Concept>) ExtentNode.get(j);
	        Concept firstConcept = firstNode.getContent();

	        //System.out.println("*** "+firstNode+" GEN: "+firstNode.getConcept().getGenerator());
	        //System.out.print("Concept:  #"+firstNode);

	        if (unfrequent.get(firstConcept) == null) {
	          e = firstConcept.getExtent().extentIntersection(newConcept.getExtent());
	          
	          if (firstNode == getLattice().getTop())
	          		tempExtent = e;
	          
	          //System.out.println("Concept:  #"+firstNode+"\t Extent Intersection: "+e);


	          if (e.size() < minSupp * nbrObjs) {
	            Iterator itr = firstNode.getChildren().iterator();
	            while (itr.hasNext()) {
	              Node<Concept> child = (Node<Concept>) itr.next();
	              unfrequent.put(child, "");
	            }
	          }

	          else {
	            //System.out.println("\t Extent Intersection: "+e);

	            Integer eSize = new Integer(e.size());
	            Hashtable ht;
	            ht = (Hashtable) vSort.get(eSize);

	            if (ht == null)
	              ht = new Hashtable();

	            Equivalence EqGen = (Equivalence) ht.get(e);

	            //Equivalence1 EqGen = (Equivalence1) table.get(e);


	            //minimal = firstNode;

	            //if (EqGen!=null)
	            //generator = EqGen.getGen();

	            if (EqGen == null)
	              EqGen = new Equivalence(firstNode);

	            if (firstConcept.getExtent().size() == e.size()) { // firstConcept is a modidied
	              Intent intentC = firstConcept.getIntent().intentUnion(newConcept.
	                  getIntent());
	              firstConcept.setIntent(intentC);
	              //System.out.println("#"+firstNode+" is modified");

	              //System.out.println(">>> #"+firstNode+" Generators before: "+firstNode.getConcept().getGenerator());
	              List vect = firstConcept.getGenerator();
	              Vector v = new Vector();
	              /*if (firstConcept.getExtent().equals(newConcept.getExtent()))
	                vect.add(newConcept.getIntent());
	              else {*/
	  
	                v = EqGen.getGen();
	              //System.out.println("x: "+v);
	                
	                if (tempExtent.equals(firstNode.getContent().getExtent())){
	                		vect.add(newConcept.getIntent());
	               }
	                else{
	                
	                for (int i = 0; i < v.size(); i++) {
	                  Intent intent = (Intent) v.elementAt(i);
	                  //System.out.println("... "+intent+" ... "+intent.union(newConcept.getIntent()));
	                  vect.add(intent.intentUnion(newConcept.getIntent()));
	                }
	              }
	                
	                //System.out.println("... "+tempExtent+" ... "+firstNode.getConcept().getExtent());
	               
	                /*if (tempExtent.equals(firstNode.getConcept().getExtent())){
	               		vect.add(newConcept.getIntent());
	               }*/
	                
	                //System.out.println("x: "+vect.size());
	              firstNode.getContent().setGenerator(vect);
	              
	              if (firstNode.equals(getLattice().getTop())){
	              	//System.out.println("Top Gen: "+getLattice().getTopConceptNode().getConcept().getGenerator());
	              	if (!vect.contains(newConcept.getIntent()))
	              	
	              	vect.add(newConcept.
	                  getIntent());
	              }
	              
	              firstNode.getContent().setGenerator(vect);
	              
	              if (firstNode.getContent().getIntent().size() ==  nbrAttrs)
	              	getLattice().setBottom(firstNode);

	              //System.out.println(">>> #"+firstNode+" Generators after: "+firstNode.getConcept().getGenerator());


	              //if (EqGen!=null)
	              //table.remove(e);

	              modifier.put(intentC, firstNode);
	              minimal = EqGen.getMinimal();
	              chiPlus.put(minimal, firstNode);
	              chiPlus.put(firstNode, firstNode);

	              //table.remove(e);
	              ht.remove(e);
	              vSort.put(eSize, ht);
	            }

	            else {

	            	Node<Concept> nTemp = EqGen.getMinimal();
	              chiPlus.put(nTemp, firstNode);
	              
	              

	              //System.out.println("("+nTemp+","+firstNode+")"+" added to chiPlus");
	              EqGen.setMinimal(firstNode);

	              //System.out.println(">>>> Intersection Properties");
	              //System.out.println("      MINIMAL: "+EqGen.getMinimal());
	              //System.out.println("      GEN: "+EqGen.getGen());
	              //System.out.println("      "+firstNode+" GEN: "+firstNode.getConcept().getGenerator());


	              /*if (EqGen.getGen().isEmpty())
	               for(int i=0;i<firstConcept.getGenerator().size();i++){
	               Intent iGen = (Intent) firstConcept.getGenerator().elementAt(i);
	                if (!iGen.isEmpty())
	                 EqGen.insertGen(iGen);
	               }*/

	              //System.out.println(">>>> UPDATE CLASS GENERATORS");
	              EqGen.updateGen(firstConcept.getGenerator());

	              //System.out.println("      New GEN: "+EqGen.getGen());

	              //table.put(e,EqGen);
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
	      //Enumeration e1 = ( Enumeration)table.keys();
	      while (e1.hasMoreElements()) {
	        Extent extent = (Extent) e1.nextElement();
	        //Equivalence1 equival = (Equivalence1) table.get(extent);
	        Equivalence equival = (Equivalence) th.get(extent);
	        Node<Concept> nodeMin = (Node<Concept>) equival.getMinimal();
	        Vector v = equival.getGen();

	        //System.out.println("#"+nodeMin.getId()+" ... "+nodeMin.getConcept().toString()+" is a genitor");
	        Intent IntGenC = nodeMin.getContent().getIntent().intentUnion(newConcept.
	            getIntent());
	        ConceptImp genC = new ConceptImp(extent, IntGenC);
	        Node<Concept> genNode = new ConceptNodeImp(genC);
	        getLattice().add(genNode);
	        
	        if (genC.getIntent().size() ==  nbrAttrs)
	        	getLattice().setBottom(genNode);

	        //System.out.println(" --- New Node: "+genC.toString()+" (Node: "+genNode.getId()+")");
	        //System.out.println(" --- New Node Intent: "+genC.getIntent());
	        lower = lowerCover(nodeMin);
	        
	        Vector minClo = minClosed(genC, minCandidate(lower, chiPlus));
	      
	        int size = minClo.size();

	        for (int i = 0; i < size; i++) {
	        	Node<Concept> coverNode = (Node<Concept>) minClo.get(i);
	          newLink(genNode, coverNode);
	          //System.out.println("New Link Between Nodes: "+genNode+" & "+coverNode);

	          if (modifier.get( (coverNode.getContent()).getIntent()) != null) {
	            dropLink(nodeMin, coverNode);
	            //System.out.println("Link Deleted Between Nodes: "+nodeMin+" & "+coverNode);
	          }
	        }
	        newLink(nodeMin, genNode);

	        getLattice().add(genNode);
	        getLattice().incNbOfNodes();
	        chiPlus.put(nodeMin, genNode);
	        //System.out.println("("+nodeMin+","+genNode+")"+" added to chiPlus");

	        Vector generator = new Vector();

	        if ( (genNode.getContent().getExtent().size() ==
	              newConcept.getExtent().size()) &&
	            (genNode.getContent().getIntent().size() >
	             newConcept.getIntent().size()))
	          generator.add(newConcept.getIntent());

	        else {

	          if (v.isEmpty())
	            generator.add(nodeMin.getContent().getIntent().intentUnion(newConcept.
	                getIntent()));

	          else
	            for (int i = 0; i < v.size(); i++) {
	              Intent intent = (Intent) v.elementAt(i);
	              generator.add(intent.intentUnion(newConcept.getIntent()));
	            }
	        }

	        genNode.getContent().setGenerator(generator);
	        //System.out.println(">>> #"+genNode+" Generators: "+genNode.getConcept().getGenerator());
	      }
	    }
	  	//System.out.println("Nombre de concepts : " + this.lcl.get_nbr_concept());
	  }

	  public Vector minCandidate(Vector lower, Hashtable chiPlus) {
	    Vector candidate = new Vector();
	    TreeMap sliceCand = new TreeMap();
	    int size = lower.size();
	    for (int i = 0; i < size; i++) {
	    	Node<Concept> node = (Node<Concept>) chiPlus.get( (Node<Concept>) lower.get(i));

	      //System.out.println("...... lower: "+lower.get(i)+" chiPlus: "+node);

	      // instruction ajoutee dernierement pour la mise a jour de l'ordre
	      if (node != null) {
	        boolean stop = false;
	        Node<Concept> node1 = node;
	        while (!stop) {
	          node = (Node<Concept>) chiPlus.get(node1);
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
	        //System.out.println("**** ("+lower.get(i)+","+node+")" +" ****");

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
//					System.out.println("candidate add "+(node.getConcept()).toString());
//					candidate.add(node);
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
	    getLattice().setUpperCover(node,childNode); //linkNodeToUpperCover(node, childNode)
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

	  /*public void saveIceberg(Node nod){
	    Iterator it = nod.getChildren().iterator();
	    while (it.hasNext()){
	     LatticeNode pt = (LatticeNode) it.next();
	     if (!visited.contains(pt)){
	      System.out.println("Concept "+pt.getId()+" properties:");
	         //pw.println("=====================");
	         System.out.println("   Extent "+ pt.getConcept().getExtent());
	         System.out.println("   Intent "+ pt.getConcept().getIntent());
	         System.out.println("   Generators "+pt.getConcept().getGenerator());
	         visited.add(pt);
	         saveIceberg(pt);
	     }
	    }
	   }*/

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
	    	Node<Concept> pt = (Node<Concept>) it.next();
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
	    //TreeMap sliceLattice =new TreeMap(new sizeCompare());
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

	      //Integer ExtentLen=new Integer(((cand.getConcept()).getExtent()).size());
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
	  			//System.out.println("Old Parent: "+ndParent);
	  			oldParents.add(ndParent);
	  		}
	  		else{
	  			//System.out.println("New Parent: "+ndParent);
	  			newParents.add(ndParent);
	  		}
	  	}
	  	
	  	/*
	  	if(!newParents.isEmpty()){
	  		Extent extent = new SetExtent();
	  		Node nd = null;
	  		Iterator its = oldParents.iterator();
	  		
	  		if (its.hasNext()){
	  			nd = (Node) its.next();
	  			extent = nd.getConcept().getExtent();
	  		}
	  		
	  		while (its.hasNext()){
	  			 nd = (Node) its.next();
	  			extent = extent.intersection(nd.getConcept().getExtent());	
	  		}
	  		
	  		if (!extent.equals(node.getConcept().getExtent())){
	  			Extent newExtent = new SetExtent();
	  			Iterator itrs = newParents.iterator();
	  			Node ndP = (Node) itrs.next();
	  			Node ndgP = (Node) table.get(ndP);
	  			
	  			if (extent.isEmpty()){
	  				node.getParents().add(ndgP);
	  				ndgP.getChildren().add(node);
	  				//System.out.println("New Link Between nodes: "+ndgP.getId()+" & "+node.getId());
	  			}
	  			
	  			else{
	  				newExtent = extent.intersection(ndgP.getConcept().getExtent());
	  				if (newExtent.equals(node.getConcept().getExtent())){
	  					node.getParents().add(ndgP);
	  					ndgP.getChildren().add(node);
	  					//System.out.println("New Link Between nodes: "+ndgP.getId()+" & "+node.getId());
	  				}
	  			}
	  			while (itrs.hasNext()){
	  				ndP = (Node) itrs.next();
	  				ndgP = (Node) table.get(ndP);
	  				newExtent = extent.intersection(ndgP.getConcept().getExtent());
	  				if (newExtent.equals(node.getConcept().getExtent())){
	  					node.getParents().add(ndgP);
	  					ndgP.getChildren().add(node);
	  					//System.out.println("New Link Between nodes: "+ndgP.getId()+" & "+node.getId());
	  				}
	  			}
	  			
	  		}
	  	}
	  	*/
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
		 //System.out.println("Concept_Attribute (a',a'') : #" +na.getId());
		  //Node geniteur = isNew(na,c.getIntent());
		  Iterator itr = Sort(na);
		  Node<Concept> genitor = null;
		  while (itr.hasNext()){
			  Vector ExtentNode = (Vector) itr.next();
			int nodeSize = ExtentNode.size();
			//System.out.println("EXTENT SIZE: "+nodeSize);
			for (int s = 0; s < nodeSize; s++) {
				Node<Concept> firstNode = (Node<Concept>) ExtentNode.get(s);
			  Concept firstConcept = firstNode.getContent();
			  genitor = isNew(firstNode,c.getIntent());
			  if (genitor == null){
				  //System.out.println("Modified Concept #"+ firstNode.getId()+" : "+firstConcept.getExtent()+" ... "+firstConcept.getIntent());
				  firstConcept.getIntent().removeAll(c.getIntent());
				  updateGen(firstConcept,c.getIntent());
				  updateOrder(firstNode,newConcepts);
			  }
			  else{
				  //System.out.println("New Concept #"+ firstNode.getId()+" : "+firstConcept.getExtent()+" ... "+firstConcept.getIntent());	
				   newConcepts.put(firstNode,genitor);
				   vect.add(firstNode);
			  }
	      
			}
		  }
	      	
			while (!vect.isEmpty()){
			  //Node nS = (Node) iter.next();
				Node<Concept> nS = (Node<Concept>) vect.elementAt(0);
			  //System.out.println("Node: "+nS.getId());
	      
	      
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
				 // System.out.println("#"+nCh+" Parents: "+nCh.getParents());
				  nCh.removeParent(nS);
				  nS.removeChild(nCh);
				  vCh.remove(0);
			  }
			  //getLattice().removeNodeFromIntentLevelIndex(nS);
			  vect.remove(0);	
			}
	  }
		  //Fin Delete-Attribute
		  
		  public void updateGen(Concept c, Intent fa){
		  
		  	Vector toDelete = new Vector();
		  	List vGen = c.getGenerator();
		  	int vSize = vGen.size();
		  	for (int i=0; i<vSize;i++){
		  		Intent intent = (Intent)vGen.get(i);
		  		if (intent.intentIntersection(fa).equals(fa))
		  			toDelete.add(intent);
		  	}
		  	vGen.removeAll(toDelete);
		  	c.setGenerator(vGen);
		  }
		  
		  
		  
		  public  void saveIceberg(Node<Concept> nod){
			
			Iterator it = nod.getChildren().iterator();
			while (it.hasNext()){
				Node<Concept> pt = (Node<Concept>) it.next();
				if (!visited.contains(pt)){
					//System.out.println("Concept "+pt.getId()+" properties:");
	 	  			//pw.println("=====================");
					//System.out.println("Extent "+ pt.getConcept().getExtent());
					//System.out.println("Ext size "+pt.getConcept().getExtent().size());
					System.out.println(pt.getContent().getIntent()+"\t"+pt.getContent().getExtent().size());
					//System.out.println("Int size "+pt.getConcept().getIntent().size());
					//System.out.println();
	 	  			visited.add(pt);
	 	  			saveIceberg(pt);
				}	
			}
		}
		  
		  public String getResults(){
			return str;
		}
}