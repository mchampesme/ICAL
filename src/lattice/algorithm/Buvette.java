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
 * Created on 2004-08-31
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package lattice.algorithm;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Date;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import java.util.Vector;


import lattice.algorithm.LatticeAlgorithmInc;
import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.ConceptNodeImp;
import lattice.util.structure.Node;
import lattice.util.trie.KLS_Trie;
import lattice.util.trie.AbstractTrie;

/**
 * @author diopmame
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class Buvette extends LatticeAlgorithmInc {
	
	
	private CompleteConceptLattice treillis ;
	public Vector col;
	
	//structures de donnees utilisees pour l'algorithme
	private AbstractTrie classesPlus = new AbstractTrie();
	private KLS_Trie classes = new KLS_Trie();
	private Stack generators = new Stack ();
	private Set mT = new HashSet();
	
	  
	  
	//Constructeur
	public Buvette (MatrixBinaryRelationBuilder br){
		super(br);
		treillis = getLattice();
		Date date = new Date();
	    System.out.println("Begin Construct ini concept from " + date.toString());
	    col = (Vector) br.getInitialObjectPreConcept(MatrixBinaryRelationBuilder.NO_SORT);
	    date = new Date();
	    System.out.println("End Construct ini concept at " + date.toString());
	    if (!col.isEmpty()) {
	      date = new Date();
	      System.out.println("Begin initialization from " + date.toString());
	      initLattice(br , col);
	      //iniLattice(col,br);
	      date = new Date();
	      System.out.println("End initialization at " + date.toString());
	    }
	   
	}
	
	//Constructeur
	public Buvette (CompleteConceptLattice lattice) {
		
		 Date date = new Date();
		    System.out.println("Begin initialization from " + date.toString());
		    setLattice(lattice);
		    date = new Date();
		    System.out.println("End initialization at " + date.toString());
		    treillis = lattice ;
	}
	
	//Constructeur
	public Buvette() {	}
	
	// initialisation du treillis avec un bottom et un top
	private void initLattice (MatrixBinaryRelationBuilder br , Vector col ){
		ConceptNodeImp.resetNodeId();
		treillis.initialiseIntentLevelIndex(br.getAttributesNumber()+1);
		
		//Je commence avec l'ensemble des objets comme top
		
		int sizeO = br.getObjectsNumber();
		
		Intent topIntent = new SetIntent();
		Extent topExtent = new SetExtent();
		FormalObject[] fo = br.getFormalObjects();
		for (int i = 0; i < sizeO; i++) {
			topExtent.add(fo[i]);
		}
		ConceptNodeImp topNode = new ConceptNodeImp(  new ConceptImp (topExtent,topIntent));
		treillis.setTop(topNode);
		treillis.incNbOfNodes() ;
		
		treillis.add(topNode);
		
		//Je commence avec l'ensemble des attributs comme bottom
		int sizeA = br.getAttributesNumber();
		
		Intent bottomIntent = new SetIntent();
		Extent bottomExtent = new SetExtent();
		FormalAttribute[] fa = br.getFormalAttributes();
		for (int i = 0; i < sizeA; i++) {
			bottomIntent.add(fa[i]);
		}
		ConceptNodeImp bottomNode = new ConceptNodeImp(   new ConceptImp (bottomExtent,bottomIntent));
		treillis.setBottom(bottomNode);
		treillis.incNbOfNodes() ;
		treillis.addBottomToIntentLevelIndex(bottomNode);
		treillis.getTop().addChild(treillis.findBottom()) ;
		treillis.getBottom().addParent(treillis.findTop()) ;
		
		
	}
	
	 private void iniLattice(Vector col, MatrixBinaryRelationBuilder br) {
	  
		Node<Concept> topNode = new ConceptNodeImp( (ConceptImp) col.get(0));
		ConceptNodeImp.resetNodeId();
		getLattice().setTop(topNode);
		getLattice().incNbOfNodes();
		getLattice().initialiseIntentLevelIndex(br.getAttributesNumber() + 1);
		getLattice().add(topNode);
		int sizeIntent = ( ( (ConceptImp) col.get(0)).getIntent()).size();
		int size = br.getAttributesNumber();
		if (size > sizeIntent) {
		  ConceptImp bottom = null;
		  Intent bottomIntent = new SetIntent();
		  Extent bottomExtent = new SetExtent();
		  FormalAttribute[] fa = br.getFormalAttributes();
		  for (int i = 0; i < size; i++) {
			bottomIntent.add(fa[i]);
		  }
		  bottom = new ConceptImp(bottomExtent, bottomIntent);
		  Node<Concept> bottomNode = new ConceptNodeImp(bottom);
		  getLattice().setBottom(bottomNode);
		  getLattice().setUpperCover(topNode, bottomNode);
		  getLattice().add(bottomNode);
		  getLattice().incNbOfNodes();
		}
		else getLattice().setBottom(topNode);
		col.remove(0);
	  }

	//Calcule la classe d'equivalence de deux concepts 
	private Concept funcQ(Concept firstConcept, Concept newConcept) {
	    Intent cBarI = (newConcept.getIntent()).intentIntersection
		(firstConcept.getIntent());
	    Extent cBarE = (firstConcept.getExtent()).extentUnion
		(newConcept.getExtent());
	    Concept cBar = new ConceptImp(cBarE, cBarI);
	    return cBar;
	    
	}
	
	// Calcule du maximum d'un concept dans le treillis 
	private Node<Concept>  getClassMax(Concept concept )
	{
	return getClassMax(concept, treillis.getBottom());	
	}
	
	//idem
	private Node<Concept>  getClassMax(Concept concept , Node<Concept> node) {
		
		Concept intersection = funcQ(concept , node.getContent());
		Intent nodeIntent = (SetIntent) node.getContent().getIntent();
		
		Node<Concept> parent = node ;
		
		Iterator parents = node.getParents().iterator();
		
		while ( parents.hasNext()){
			
			node = (Node<Concept>)parents.next();
			nodeIntent = (SetIntent) node.getContent().getIntent();
			intersection = funcQ(concept , node.getContent());
			
			if( intersection.getIntent().size()== concept.getIntent().size())
				return getClassMax(concept , node) ;
		}
		return parent ;
	}
	 
	// Verifie si un concept est un geneateur ou pas
	private boolean isGenerator (Concept concept , Concept newConcept){
		if ( newConcept.getIntent().toString().equals(
				concept.getIntent().toString()))
			return false ;
		else
			return true ;
	}
	
	//Verifie si largeConcept genere smallConcept
	private boolean generate ( Concept largeConcept , Concept  smallConcept ) {
		
		if ( funcQ(largeConcept,smallConcept).getIntent().size()==
				 smallConcept.getIntent().size())
			return true ;
		
		return false ;
	}
	
	// Retourne la liste des minima d'un concept
	private List minima ( Stack candidates , Concept concept){
		List min = new ArrayList() ;
		int i = 0 , j = 0 ;
		
		
		Node<Concept>  minima = (Node<Concept>)candidates.elementAt(0);
		
		while ( i < candidates.size()) {
			if (concept.getIntent().size() > 
					((Node<Concept>)candidates.elementAt(i)).getContent().getIntent().size()){
					if ( minima.getContent().getIntent().size() >
							((Node<Concept>)candidates.elementAt(i)).getContent().getIntent().size())
						minima = (Node<Concept>)candidates.elementAt(i);
					if ( !min.contains((Node<Concept>)candidates.elementAt(i))){
						min.add(candidates.elementAt(i)) ;
					}
			}
			i++ ;
		}
		for ( i = 0 ; i < min.size() ; i++){
		
			 minima  = ((Node<Concept>)min.get(i));
			 
			for ( j = i+1 ; j < min.size() ; j++ ){
				
					if ( minima.getContent().getIntent().size()>
							((Node<Concept>)min.get(j)).getContent().getIntent().size()	){
						if(generate(minima.getContent(),
							((Node<Concept>)min.get(j)).getContent()) ){
							min.remove(j);
						
						}
					}else
					if ( minima.getContent().getIntent().size()<
							((Node<Concept>)min.get(j)).getContent().getIntent().size()	){
						if(generate(((Node<Concept>)min.get(j)).getContent()
								,minima.getContent())){
							min.remove(i);	
						}
					}
				}
			}
		
		
		
		return min ;
	}
	
	
	//Retourne le noeud dans le treillis qui contient le concept
	private Node<Concept> getNodeVaue ( Concept concept ){
		//System.out.println("concept: "+concept.getExtent()+" ... "+concept.getIntent());
		List<List<Node<Concept>>> latticeContent = treillis.getIntentLevelIndex();
		List<Node<Concept>> levelContent = latticeContent.get(concept.getIntent().size()) ;
		int i = 0  ;
		while (i < levelContent.size() ){
			
			if ( levelContent.get(i).getContent().getIntent().equals(
					concept.getIntent()))
				return levelContent.get(i) ;
			i++;
		}
		
		
		return new ConceptNodeImp (new ConceptImp (new SetExtent() , new SetIntent()));
	}
	
	// Met a jour le treillis
	private void updateOrder(Concept newConcept ,Node<Concept> child){
		
		
	Stack candidates = new Stack();
	// ajouter le nouveau noeud
	Iterator parents = child.getParents().iterator();
	List trueCovers ;
	Node<Concept> conceptNode , node ;
	ConceptNodeImp newConceptNode ;
	Concept concept ;
	int i = 0 ;
	
	newConceptNode = new ConceptNodeImp ((ConceptImp) funcQ(newConcept ,child.getContent()));
	
	//System.out.println(newConceptNode+" is a new concept");
	
	
	
	while (parents.hasNext()){
		node = (Node<Concept>)parents.next();
		
		Intent intC = funcQ(newConcept,node.getContent()).getIntent();
		
		if((classesPlus.contains(intC)== null)|| (classesPlus.contains(intC) == classesPlus.getRoot()))
			concept = new ConceptImp (new SetExtent(),new SetIntent());
			
		else
		 concept = (Concept) ((classesPlus.contains(intC)).getData());
		
		
		//System.out.println("concept: "+concept.getExtent()+" ... "+concept.getIntent());
		//concept = (Concept)classesPlus.get(funcQ(newConcept,node.getConcept()));
	
		conceptNode = getNodeVaue (concept);
		
		//System.out.println("node: "+node.getId()+" ... conceptNode: "+conceptNode.getId());
		
		candidates.add(conceptNode);
	}
	
	
		trueCovers = minima(candidates , newConcept);
	
	i = 0 ;	
	
	while ( i < trueCovers.size() ) {
		
		conceptNode = (Node<Concept>)trueCovers.get(i) ;
		
		treillis.remove(conceptNode) ;
		conceptNode.addChild(newConceptNode) ;
		newConceptNode.addParent(conceptNode) ;
		
		//System.out.println("New Link between "+newConceptNode+ "& "+conceptNode);
		if ( conceptNode.getChildren().contains(child)){
			conceptNode.removeChild(child) ;
			child.removeParent(conceptNode) ;
		}
		treillis.add(conceptNode) ;
		
		if(mT.contains(conceptNode.getContent())){
			child.removeChild(conceptNode) ;
			
		}
		i++;
	
	}
	
	
	newConceptNode.addChild(child);
	
	
	if ( newConceptNode.getParents().size() == 0 ){
		newConceptNode.addParent(treillis.getTop()) ;
		treillis.getTop().addChild(newConceptNode) ;
	}
	child.addParent(newConceptNode) ;
	treillis.add(newConceptNode) ;
	treillis.incNbOfNodes() ;
	treillis.remove(child) ;
	treillis.add(child) ;
	
	
	
	}
	
	
	// Ajoute un objet dans le treillis
	private void addObject (Concept newConcept){
		boolean content = false ;
		
		Concept longestKey = null , nextConcept  ;
		Node<Concept> generatedConcept , classMax;
	
		Iterator parents ;

		generators = new Stack() ;
		mT = new HashSet();
		
		// preProcess 
		Concept bottom =  treillis.getBottom().getContent();
		Concept concept = funcQ(bottom,newConcept);	
		//classes.put(concept);
		classes.add(concept.getIntent(),concept);
		
			
		while ( content == false ) {
			longestKey = (Concept)classes.getLongestKey() ;
			 if (longestKey == null)
			 	content = true;
			
			else{
			Intent intent = longestKey.getIntent();
			
			
			
			
		
			 //intent = (Intent)classes.getLongestKey() ;
			classMax = getClassMax(longestKey);
			
			//System.out.println("longestKey: "+intent+" ... classMax: "+classMax.getId());
			
			parents = classMax.getParents().iterator();
			
			
			if ( isGenerator (classMax.getContent() ,longestKey)){
				
				
				if ( !generators.contains(classMax))
					generators.add(classMax);
				
			}
			
			else{
				
				//System.out.println(classMax.getId()+ " is modified");
				mT.add(classMax.getContent());
				//classesPlus.put(longestKey);
				classesPlus.add((Collection)longestKey.getIntent(),(Object)longestKey);
				
				
				
				treillis.remove(classMax);
				classMax.getContent().setExtent(classMax.getContent()
						.getExtent().extentUnion(longestKey.getExtent())) ;
				
				
				treillis.add(classMax);
				treillis.setBottom(treillis.findBottom()) ;
					
					
			}
			
			while(parents.hasNext() == true) {
				concept = ((Node<Concept>)parents.next()).getContent() ;
				nextConcept = funcQ(newConcept,concept); 
				//classes.put_update(nextConcept);
				classes.add(nextConcept.getIntent(),nextConcept);
					 
			}
			content = classes.isEmpty() ;
			}
	   }
				
		
		/*creer les nouveaux concepts qu'on a dans le generateur
			 *et les ajouter dans le treillis 
			 *les ajouter aussi dans classesPlus */
		while (generators.isEmpty()== false){
			
			generatedConcept =(Node<Concept>)generators.pop() ;
			updateOrder(newConcept,generatedConcept);
			
			
			//classesPlus.put(funcQ(newConcept,generatedConcept.getConcept()));
			Concept c = funcQ(newConcept,generatedConcept.getContent());
			
			classesPlus.add(c.getIntent(),c);		
					
		}
	}
	
	
	private void doIncre (Vector col){
		 int size = col.size();
		    int j = 1;
		    Date date = new Date();
		    System.out.println("Add the first object at " + date.toString() + "\n");
		    for (int i = 0; i < size ; i++) {
		    	 
		      if (i == j * 500) {
		        j++;
		        date = new Date();
		        System.out.println(date.toString() + "\n");
		      }
		      System.out.println("Add  o: " + ((ConceptImp) col.get(i)).getExtent()+" ... o': "+((ConceptImp) col.get(i)).getIntent());
		       addObject((ConceptImp) col.get(i));
		     
		      sendJobPercentage(i*100 / col.size());
		    }
		    date = new Date();
		    
		    Node<Concept> topNode = (Node<Concept>)treillis.getTop();
		    Iterator itr = topNode.getChildren().iterator();
		    boolean found =false;
		    
		    while ((itr.hasNext()) && !found){
		    	Node<Concept> topChild = (Node<Concept>) itr.next();
		    	if(topChild.getContent().getExtent().size() == topNode.getContent().getExtent().size()){
		    		found = true;
		    		topNode.removeChild(topChild);
		    		topChild.removeParent(topNode);
		    		treillis.setTop(topChild);
		    	}
		    }
		    System.out.println("Finish the algorithm at " + date.toString());
		    System.out.println("Number of concepts : " + treillis.size());
		    
		   
		}
	
	
	
	public void doAlgorithm() {
		long time = System.currentTimeMillis();
		doIncre(col);
		long time2 = System.currentTimeMillis() - time;
	}
	
	
	public void addConcept(Concept c) {
		addObject(c);
		
	}

	public String getDescription() {
		return "Bottom-Up VErtical laTTice updatE ";
	}
	
//	method added by Mame Awa Diop

	  public long standAloneRunning (MatrixBinaryRelationBuilder  br ) {
		long time = System.currentTimeMillis();
		
	  	
	  	col = (Vector) br.getInitialObjectPreConcept(MatrixBinaryRelationBuilder.NO_SORT);
	    if (!col.isEmpty()) {
	      initLattice(br, col);
	    	//iniLattice(col,br);
	    }
	 
	    doAlgorithm();
	    return (System.currentTimeMillis() - time) ;
	  }
}
