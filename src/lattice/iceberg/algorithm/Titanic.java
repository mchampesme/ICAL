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
 * Created on 2004-10-11
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package lattice.iceberg.algorithm;

/**
 * @author 
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
//Titanic.java - class that controls the generation of closed frequent itemsets

/*$Id: Titanic.java,v 1.2 2004/10/26 19:41:40 olivezuo Exp $*/
/**
 * @author  Laszlo Szathmary (<a href="szathmar@loria.fr">szathmar@loria.fr</a>)
 */

import java.util.*;
import java.io.*;

import lattice.algorithm.LatticeAlgorithm;
import lattice.util.*;
import lattice.util.concept.*;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
import lattice.util.titanic.Key;
import lattice.util.titanic.Level;
import lattice.util.titanic.FCIRow;
import lattice.util.trie.*;


public class Titanic extends LatticeAlgorithm
{
	double minsupport;                        // min_support
	
   Runtime rt = Runtime.getRuntime();     // to check memory usage
   
   Vector P_vector  = new Vector();
   Intent null_closure;                   // closure of the empty set in P_0
  Vector keysOfK1 = new Vector();        // it'll contain the frequent attributes
   AbstractTrie allKeysTrie;                      // we'll store the keys (minimal generators) in this
   
   private Vector col;
   private List<FormalAttribute> attributes;
   
   private Hashtable concepts = new Hashtable();
   private Hashtable conceptAttribute = new Hashtable();
   

   public Titanic(MatrixBinaryRelationBuilder br, double minsupport)
   {
   	  super(br);
      int max_attr;
      this.minsupport = minsupport;
      this.allKeysTrie = new AbstractTrie();
   }

 
   
   public void start()
   {
      int k = 0;
      Level p_0, p_1, p_k, p_km1;
      
      init_P_0(p_0 = new Level());
      //System.out.println("P_0 init:\n"+p_0);
      P_vector.add(p_0);            // P_0 is registered

      k=1;
      init_P_1(p_1 = new Level());
     // System.out.println("P_1 init:\n"+p_1);
      P_vector.add(p_1);            // P_1 is registered


      for(;;)  // we'll break out from this loop from inside
      {
         p_k = (Level)P_vector.get(k);     // the current P_k table
         weigh(p_k, this.minsupport);
         //System.err.println("P_"+k+":\n"+p_k);

         p_km1 = (Level)P_vector.get(k-1); // P_k-1
         closure(k, P_vector);
         // later we will need the closure of the empty set, let's save it in a global variable
         if (k==1) this.null_closure = ((FCIRow)p_0.getRows().get(0)).getClosure();
         //System.err.println("P_"+(k-1)+" closure utan:\n"+p_km1);
         fill_Key_and_Key_prime(p_k);
         p_k.prune();
//         System.gc();
//System.err.println("P_0:\n"+p_0);
//System.err.println("P_"+k+":\n"+p_k);
         
         if (p_k.getKeyPrime().getKeys().isEmpty()) break;
//         if (p_k.getKeyPrime().getKeys().isEmpty() || p_k.getKey().getKeys().isEmpty()) break;
         // break out of the loop if: 1) in K_k all the elements has support value (-1)
         //                              i.e. if K_k' is empty, or
         //                           2) if K_k is an empty set
         ++k;
         P_vector.add(p_k = new Level());  // the new table
         p_km1 = (Level)P_vector.get(k-1); // P_k-1
         //System.out.println("P_"+(k-1)+":\n"+p_km1);
         //System.err.println("P_"+k+":\n"+p_k);
         titanic_gen(k-1, p_k, p_km1);
         //System.err.println("P_"+k+":\n"+p_k);
      }
     // System.err.println("__END__");
      
   }
         
   private void titanic_gen(final int i, Level p_k, Level p_km1)
   {
      Key keys      = p_km1.getKey();
      Key key_prime = p_km1.getKeyPrime();
      FormalAttribute[][] generators = key_prime.getGenerators();      // get the generators of K_k-1' in a 2D-array
      int l, k, c;
      Vector subsets;
      Enumeration e;
      Vector sub;
      FCIRow row;
      Vector candidate;
      int sub_supp;        // support of the subset
      int min_pred_supp;
      
      

      for (l = 0; l < generators.length-1; ++l)
      {
         middle:
         for (k = l+1; k < generators.length; ++k)
         {
            for (c = 0; c < i-1; ++c)
            
               if ( generators[l][c] != generators[k][c] ) {
               	break middle;  // if they are not equal
               }
                                                                          // continue in the 1st column       
        //System.out.println(generators[l][i-1]+" ... "+generators[k][i-1]+" ... "+CompareToAsNumeric(generators[l][i-1],generators[k][i-1]));
            //if (generators[l][i-1].CompareToAsNumeric(generators[k][i-1])<0)   // OK, if the 1st number < the 2nd
            if(CompareToAsNumeric(generators[l][i-1],generators[k][i-1])<0)  
            {  
               candidate = p_k.createCandidate(generators[l], generators[k][i-1]);
               

               min_pred_supp = Integer.MAX_VALUE;  // init
               subsets = p_k.get_i_subsets(candidate);      // vector of sets of one-size smaller subsets
               for (e = subsets.elements(); e.hasMoreElements(); )
               {
                  sub = (Vector)e.nextElement();
                  // test the candidate, if passed => add
                  //if ( (keys.getTrie().contains(sub) == false) )
                  if ( (p_km1.getTrie().contain(sub) == false) )
                     continue middle;
                  // else
                  sub_supp = p_km1.getRowByGen(sub).getSupport();
                  min_pred_supp = Math.min(min_pred_supp, sub_supp);
               }
               row = new FCIRow(candidate);
               row.setPredSupp(min_pred_supp);
               p_k.add_row(row);
            }
         }
      }
   }

   private void fill_Key_and_Key_prime(Level p_k)
   {
      FCIRow row;
      for (Enumeration e = p_k.getRows().elements(); e.hasMoreElements(); )
      {
         row = (FCIRow)e.nextElement();
         if (row.getSupport() != row.getPredSupp()) 
         {
            p_k.addKey(row);
            row.setIsKey(true);
            this.allKeysTrie.add(row.getGen(), row);
         }
      }
      p_k.fillKeyPrime();
   }

   private void closure(final int k, Vector P_vector)
   {
   	Date closureTime = new Date();
      //System.err.println("Start: calculating closures"+"\t"+closureTime.toString());
      Level p_k   = (Level)P_vector.get(k),
        p_km1 = (Level)P_vector.get(k-1);
//        p_km2 = ((k>=3)?((P)P_vector.get(k-2)):(null));      // P_k-2, it has sense if k>=2

      //System.err.println("*** k: "+k);
      FCIRow row;
     Intent closure;

      for (Enumeration e = p_km1.getKeyPrime().getKeys().elements(); e.hasMoreElements(); )
      {
         row = (FCIRow)e.nextElement();
         closure = getClosure(k, row, p_k, p_km1);    // closure in P_k-1
//         closure = getClosure(k, row, p_k, p_km1, p_km2);    // closure in P_k-1
         row.setClosure(closure, p_km1);
         
        if(row.getClosure().size() > 0){
        	
        	
        	ConceptNode nCurrent = (ConceptNodeImp) concepts.get(row.getExtent());
         
         if (nCurrent  == null){
         	getLattice().incNbOfNodes();
         	ConceptImp cCurrent ;
         	cCurrent = new ConceptImp(row.getExtent(),row.getClosure()); 
         	nCurrent = new ConceptNodeImp(cCurrent);
         	
         }
          if (row.getClosure().size() == 0){
          	 
             Extent topExtent = new SetExtent();
             ConceptImp topConcept;
             FormalObject[] fobj = this.getBinaryRelation().getFormalObjects();
             	
             for(int i=0; i< this.getBinaryRelation().getObjectsNumber();i++){
             	FormalObject  fo = fobj[i];
             	topExtent.add(fo);
             }
            
             nCurrent.getContent().setExtent(topExtent);
             getLattice().setTop(nCurrent);
             //concepts.put(nCurrent.getConcept().getExtent(),nCurrent);
             
          }
          
          if ((row.getExtent().size() == this.getBinaryRelation().getObjectsNumber()) && (getLattice().getTop()== null)){
          	getLattice().setTop(nCurrent);
            concepts.put(nCurrent.getContent().getExtent(),nCurrent);
         }
        
         List v = nCurrent.getContent().getGenerator();
         v.add(row.getGenerator());
         //System.out.println(row.getGenerator()+" ... "+nCurrent.getConcept().getExtent());
         nCurrent.getContent().setGenerator(v);
         
         concepts.put(nCurrent.getContent().getExtent(),nCurrent);
         
         if (row.getGen().size() == 1){
         	Vector vect = row.getGenerator();
         	Intent intent = new SetIntent();
         	
         	for (int i=0;i<vect.size();i++){
         		FormalAttribute att = (FormalAttribute) vect.elementAt(i);
         		intent.add(att);
         	}
         	
         	conceptAttribute.put(intent,nCurrent);
         	//System.out.println(row.getGenerator()+" ... "+nCurrent);
         }
         
         /*if (nCurrent.getConcept().getExtent().size() == this.binRel.getObjectsNumber()){
         	Node nTop = getLattice().getTop();
         	if (nTop == null)
         		getLattice().setTop(nCurrent);
         }*/
         
         //System.out.println(row);
         //System.out.println(row.getGen()+"\t"+row.getSupport()+"\t"+row.getPredSupp()+"\t"+row.getIsKey()+"\t"+row.getClosure()+"\t"+row.getExtent());
         
         //System.out.println(nCurrent.getId()+"\t"+nCurrent.getConcept().getExtent()+"\t"+nCurrent.getConcept().getIntent()+"\t"+nCurrent.getConcept().getGenerator());
      }
   }
   
      closureTime = new Date();
      //System.err.println("End:   calculating closures"+"\t"+closureTime.toString());
   }

   private Intent getClosure(Vector xmm) 
   {
   	Level p = (Level)this.P_vector.get(xmm.size());

      return ((FCIRow)p.getRowByGen(xmm)).getClosure();
   }

   private Intent getClosure(final int k, FCIRow key_row, Level p_k, Level p_km1)
//   private BitSet getClosure(final int k, Row_p key_row, P p_k, P p_km1, P p_km2)
   {
//System.err.println("=================");      
      Vector x = key_row.getGen();
      int x_support = ((FCIRow)p_km1.getRowByGen(x)).getSupport();
     // System.out.println((FCIRow)p_km1.getRowByGen(x)+" ... x_support: "+x_support);
     //System.out.print("\t X: "+x);      
      Vector y = (Vector)x.clone();
      //System.out.println("\t Y: "+y);      
      Vector xmm;     // X\{m}, (X\{m}).closure
      Intent xmm_closure;
      int i;
      FCIRow row;
      
      Iterator itr = (Iterator)x.iterator();
      while(itr.hasNext()){
      	FormalAttribute fa = (FormalAttribute) itr.next();
         xmm = (Vector)x.clone();
         xmm.remove(fa);             // it is now a one-size smaller subset of X
        //System.out.println("\t m: "+ fa+" ... X\\{m}: "+xmm);
         xmm_closure = getClosure(xmm);
         y.addAll(xmm_closure);
      }
  //System.out.println("\t(1) Y after extension: "+y);      
      
      Vector all_minus_y = (Vector)this.keysOfK1.clone();
      all_minus_y.removeAll(y);        // K1 (all frequent attributes, present in the keys of P_1, i.e. K_1) \ Y
    // System.out.println("\t K_1\\Y: "+all_minus_y);      

      Vector xum; // X unio m
      int s = -1;      // support, -1 is for the compiler not to complain
      Vector subsets;
      int min, curr_support;
      Enumeration e;
      Vector sub, elem;
      int sub_size;
      
      Iterator iter = (Iterator) all_minus_y.iterator();

      while (iter.hasNext()){
      	FormalAttribute fat = (FormalAttribute)iter.next();
      	Vector xumSorted = (Vector)x.clone();      // now it's equal with X
         xumSorted.add(fat);                   // now it's X unio m
          xum = new Vector();
         xum = this.SortAsNumeric(xumSorted);
        //System.out.println("\t m: "+fat+" ... X unio m: "+xum);      
         row = (FCIRow)p_k.getRowByGen(xum);
         if (row != null){   /* if C_k contains xum */   
         	s = row.getSupport();
         	//System.out.println("\t in C: "+row.getGenerator()+" ... s: "+s); 
         }
         else
         {
            min = Integer.MAX_VALUE;
//            subsets = p_km1.getKey().getTrie().getSubsetsOf(xum);
            subsets = this.allKeysTrie.getSubsetsOf(xum);
            
            //System.out.println("\t not in C. ");
            // end:   if the subset only has one element and this element is equal to X
            for (e = subsets.elements(); e.hasMoreElements(); )
            {
               sub = ((FCIRow)e.nextElement()).getGen();
              
               sub_size = sub.size();
               curr_support = ((Level)this.P_vector.get(sub_size)).getRowByGen(sub).getSupport();
            // on: lehet hulyeseg
//                if (sub.get(i)==false) break;
            // off: lehet hulyeseg
//                  curr_support = ((Row_p)p_km1.getRowByGen(sub)).getSupport();
               if (curr_support < min) min = curr_support;  // find the minimum support between them
            }
            s = min;
         }
         //System.err.println("s: "+s);      
         if (s == x_support) {
         	y.add(fat);
         	 //System.err.println("y : "+y);    
         }
         	
      }
     //System.out.println("y at the end: "+y); 

      Intent x_closure = new SetIntent();
      
      for(int h=0;h<y.size();h++){
      	FormalAttribute fa = (FormalAttribute)y.elementAt(h);
      	x_closure.add(fa);
      }

      //System.out.println("y at the end: "+x_closure.toString()); 
      return x_closure;
      
   }

   private Vector clean_subsets_from_low_support(Vector subsets)
   {
      Vector to_delete = new Vector();
      FCIRow row;

      for (Enumeration e = subsets.elements(); e.hasMoreElements(); )
      {
         row = (FCIRow)e.nextElement();
         if (row.getSupport() < (this.minsupport* this.getBinaryRelation().getObjectsNumber())) to_delete.add(row);
      }
      subsets.removeAll(to_delete);
      
      for (int i=0;i<to_delete.size();i++){
      	FCIRow r = (FCIRow)to_delete.elementAt(i);
      	Extent e = r.getExtent();
      	concepts.remove(e);
      }
      

      return subsets;
   }

   private void weigh(Level p_k, final double minsupport)
   {
   	Date weighTime = new Date();
      if (p_k.isEmpty()) return;
      //System.err.println("Start: calculating weights"+"\t"+weighTime);
      // else
      Intent itemset;
      Vector subsets;
      AbstractTrie trie = p_k.getTrie();
      Enumeration e, in;
      FCIRow row;
      Extent extention ;

      for (int i = 0; i < col.size(); i++ )
      {
      	Concept c = (ConceptImp)col.get(i);
      	itemset = c.getIntent();
      	
      	TreeSet temp = new TreeSet();
      	Iterator itr = itemset.iterator();
      	while(itr.hasNext()){
      		FormalAttribute fa = (FormalAttribute)itr.next();
      		if (fa.getName().startsWith("att_")){
      			FormalAttribute FA = new DefaultFormalAttribute(fa.getName().substring(4,fa.getName().length()));
      			temp.add(new Integer(FA.getName()));
      		}
      	}
      	Vector itemset_vector = new Vector();
      	itr = temp.iterator();
      	
      	if (!temp.isEmpty()){
      		while (itr.hasNext()){
      			FormalAttribute faSort = new DefaultFormalAttribute("att_"+((Integer)itr.next()).toString());
      			itemset_vector.add(faSort);
      		}
      		//subsets = trie.getSubsetsOf(itemset_vector);
      	}
      	else
      		itemset_vector.addAll(itemset);
      	
      	subsets = trie.getSubsetsOf(itemset_vector);
      		//System.err.println("itemset: "+itemset);
         for (in = subsets.elements(); in.hasMoreElements(); )
         {
            row = (FCIRow)in.nextElement();
            //System.err.println("   "+row.getGen());
            row.incSupport();
            
            extention = new SetExtent();
            extention = row.getExtent();
            extention = extention.extentUnion(c.getExtent());
            row.setExtent(extention);
         }
      }

      for (e = p_k.getRows().elements(); e.hasMoreElements(); )
      {
         row = (FCIRow)e.nextElement();
         if (row.getSupport() < (this.minsupport* this.getBinaryRelation().getObjectsNumber())){
         	row.setSupport(-1);
         	
         	Extent extent = row.getExtent();
         	concepts.remove(extent);
         }
         	
      }
      weighTime = new Date();
     // System.err.println("End:   calculating weights"+"\t"+weighTime);
   }

   private void init_P_0(Level p) {
      FCIRow row = new FCIRow();      // P_0 will have just one row. Its generator contains the empty set (constructor of the class did it)
      
    	//row.setSupport(1);            // support of the empty set is 0
        
    	//row.setSupport(this.binRel.getObjectsNumber());
    	row.setSupport(Integer.MAX_VALUE);
    	row.setIsKey(true);
    	
    	 p.add_row(row);
         p.addKey(row);
         p.fillKeyPrime();
         
    }
      
   

   private void init_P_1(Level p)
   {
      Vector gen;
      FCIRow row;
      
      //System.out.println("attributes.size(): "+attributes.size());
      
      for (int i = 0; i<attributes.size(); i++) 
      {
         gen = new Vector();
         FormalAttribute fa = (FormalAttribute) attributes.get(i);
         //System.out.println(fa);
         gen.add(fa);
         row = new FCIRow(gen);
         //row.setPredSupp(1);
         row.setPredSupp(this.getBinaryRelation().getObjectsNumber()+1);
         p.add_row(row);
         //
         this.keysOfK1.add(fa);
         this.allKeysTrie.add(gen, row);
      }
    
   }



/* (non-Javadoc)
 * @see lattice.algorithm.LatticeAlgorithm#doAlgorithm()
 */
public void doAlgorithm() {
	col = (Vector) this.getBinaryRelation().getInitialObjectPreConcept(MatrixBinaryRelationBuilder.NO_SORT);
	attributes = this.getBinaryRelation().getAttributes();
	
	
	this.start();
	
	if (getLattice().getTop() == null){
		Extent topExtent = new SetExtent();
	     ConceptImp topConcept;
	     FormalObject[] fobj = this.getBinaryRelation().getFormalObjects();
	     	
	     for(int i=0; i< this.getBinaryRelation().getObjectsNumber();i++){
	     	FormalObject  fo = fobj[i];
	     	topExtent.add(fo);
	     }
	     
	     topConcept = new ConceptImp(topExtent,new SetIntent());
	     topConcept.setGenerator(new Vector());
	     
	     ConceptNode topNode = new ConceptNodeImp(topConcept);
	     getLattice().setTop(topNode);
	     concepts.put(getLattice().getTop().getContent().getExtent(),getLattice().getTop());
	}
	//System.out.println("concepts.size(): "+concepts.keySet().size());
	
	/*Iterator itr = concepts.keySet().iterator();
	while(itr.hasNext()){
		Extent e = (Extent)itr.next();
		ConceptNode node = (ConceptNode)concepts.get(e);
		System.out.println(node.getId()+"\t"+e.toString()+"\t"+node.getConcept().getGenerator()+"\t"+node.getConcept().getIntent());
	}
		
	 itr = conceptAttribute.keySet().iterator();
	while(itr.hasNext()){
		Intent e = (Intent)itr.next();
		ConceptNode node = (ConceptNode)conceptAttribute.get(e);
		System.out.println(e.toString()+"\t"+node.getId());
	}*/
	
   this.NR_Gen_Hasse(concepts,conceptAttribute, attributes);
    
    System.out.println("Nbr of Concepts: " + getLattice().size());
}



/* (non-Javadoc)
 * @see lattice.algorithm.LatticeAlgorithm#getDescription()
 */
public String getDescription() {
	 return "Titanic - Concept Lattice version";
}

public void NR_Gen_Hasse(Hashtable concepts, Hashtable conceptAttribute, List<FormalAttribute> M){
	
	//System.out.println("M : " + M);
	
	Hashtable Counter = new Hashtable();
	
	Iterator it = concepts.keySet().iterator();
	
	while (it.hasNext()){
	  Vector listeConceptsCandidats = new Vector();
	  ConceptNode cCourant = (ConceptNodeImp) concepts.get(it.next());
	 //System.out.println("\n ci : " + cCourant.getId()+"\tExtent: "+cCourant.getConcept().getExtent()+"\tIntent: "+cCourant.getConcept().getIntent());
	  
	 // System.out.println("M-A : " + calculDifference(M, cCourant.getConcept().getIntent()));
	  //System.out.println("ci : " + cCourant.getId());
	  Iterator itD = calculDifference(M, cCourant.getContent().getIntent()).iterator();
	  while (itD.hasNext()) {
		FormalAttribute a = (FormalAttribute) itD.next();
	
		
		Intent in = new SetIntent();
		in.add(a);
		
		//System.out.println("att: "+in+" ConceptAttrib: "+((LatticeNode) conceptAttribute.get(in)).getId());
		
		
		Extent extConceptAtt = new SetExtent();
		Extent E = new SetExtent();
		
		ConceptNode conceptAttNode = (ConceptNodeImp)conceptAttribute.get(in);
		if (conceptAttNode !=null){
		
		extConceptAtt = ((ConceptNode)conceptAttribute.get(in)).getContent().getExtent();
	
		E = extConceptAtt.extentIntersection(cCourant.getContent().getExtent());	
		
	   //System.out.println("att: "+a+" Intersect: "+E);
		//if (E.size() != 0) {
		ConceptNode candidat = (ConceptNodeImp) concepts.get(E);
		  //System.out.println("cand : " + candidat.getId());
		  if (candidat != null){
		  	Integer cCounter = (Integer) Counter.get(candidat);
		  	if(cCounter == null)
		  		cCounter = new Integer(0);
			
		  	int cCount = cCounter.intValue();
		  	cCount++;
		  	
		  	//System.out.println(candidat.getId()+" ... counter: "+cCount);
		  	
			Counter.put(candidat,new Integer(cCount));
			
			cCount = ((Integer)Counter.get(candidat)).intValue();
			
			if (cCount == 1) 
				listeConceptsCandidats.add(candidat);
			
			//System.out.println("(1): "+(cCount + cCourant.getConcept().getIntent().size())+" ... (2): "+ (candidat.getConcept().getIntent().size()));
			
			if (cCount + cCourant.getContent().getIntent().size() == candidat.getContent().getIntent().size()) {
			  newLink(cCourant,candidat);
			  //System.out.println("New Link between: "+cCourant.getId()+" & "+candidat.getId());
			}
		  }
		}
	  }
	  Counter.clear();
	}
  }

private void newLink(ConceptNode node,ConceptNode childNode) {
    getLattice().setUpperCover(node, childNode);
  }

private List<FormalAttribute> calculDifference(List<FormalAttribute> m, Intent intent){
    List<FormalAttribute> v = new Vector<FormalAttribute>(m);
	Iterator itr = intent.iterator();
	while (itr.hasNext()){
		FormalAttribute fa = (FormalAttribute)itr.next();
		v.remove(fa);
	}
	
	return v;
}

private int CompareToAsNumeric(FormalAttribute a, FormalAttribute b){
	
	if ((a.getName().startsWith("att_")) && (b.getName().startsWith("att_"))){
		Integer aInt = new Integer(a.getName().substring(4,a.getName().length()));
		Integer bInt = new Integer(b.getName().substring(4,b.getName().length()));
		//System.out.println(aInt+" --- "+bInt+" --- "+aInt.compareTo(bInt));
		return (aInt.compareTo(bInt));	
	}
	
	/*Character first = new Character(a.getName().charAt(0));
	if (first.isDigit(first.charValue())){
		Integer aInt = new Integer(a.getName());
		Integer bInt =  new Integer(b.getName());
		return (aInt.compareTo(bInt));	
	}*/
	
	else
		return (a.compareTo(b));
	
}

private Vector SortAsNumeric(Vector v){
	TreeSet temp = new TreeSet();
	FormalAttribute fa ;
  	
  	for(int i=0;i<v.size();i++){
  		 fa = (FormalAttribute)v.elementAt(i);
  		if (fa.getName().startsWith("att_")){
  			FormalAttribute FA = new DefaultFormalAttribute(fa.getName().substring(4,fa.getName().length()));
  			temp.add(new Integer(FA.getName()));
  		}
  		else
  			temp.add(fa);
  	}
  	Vector itemset_vector = new Vector();
  	Iterator itr = temp.iterator();
  	
  	fa = (FormalAttribute)v.elementAt(0);
  	if (fa.getName().startsWith("att_")){
  		while (itr.hasNext()){
  			FormalAttribute faSort = new DefaultFormalAttribute("att_"+((Integer)itr.next()).toString());
  			itemset_vector.add(faSort);
  		}
  	}
  	else{
  		while (itr.hasNext()){
  			FormalAttribute faSort = (FormalAttribute) itr.next();
  			itemset_vector.add(faSort);
  		}	
  	}
  	
  	
  	return (itemset_vector);
}


}


