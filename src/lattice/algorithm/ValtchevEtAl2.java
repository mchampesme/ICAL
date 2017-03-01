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

import java.util.Collection;
import java.util.Date;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.TreeMap;
import java.util.Vector;

import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
import lattice.util.structure.Node;
import rule.generator.Jen;
import rule.generator.ValtchevAlOnlineGeneratorUpdate;

/**
 * @author frambouc
 *
 * To change this generated comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */

public class ValtchevEtAl2
    extends LatticeAlgorithmInc {

  private Vector col;
  public static Hashtable cGen;
  private boolean generators = true;

  // section added by Amine
  public ValtchevEtAl2(MatrixBinaryRelationBuilder br) {
  	this(br,true);
  }
  
  /**
   * @param br
   * @param gens
   */  
  
  public ValtchevEtAl2(MatrixBinaryRelationBuilder br, boolean gens) {
    super(br);
    generators = gens;
    Date date = new Date();
    System.out.println("Begin Construct ini concept from " + date.toString());
    col = (Vector) br.getInitialObjectPreConcept(MatrixBinaryRelationBuilder.NO_SORT);
    date = new Date();
    System.out.println("End Construct ini concept at " + date.toString());
    if (!col.isEmpty()) {
      date = new Date();
      System.out.println("Begin initialization from " + date.toString());
      iniLattice(col, br);
      date = new Date();
      System.out.println("End initialization at " + date.toString());
    }
    cGen = new Hashtable();
  }
  
// section end
  public ValtchevEtAl2(CompleteConceptLattice l) {
    Date date = new Date();
    System.out.println("Begin initialization from " + date.toString());
    setLattice(l);
    date = new Date();
    System.out.println("End initialization at " + date.toString());
    cGen = new Hashtable();
  }

  public void addConcept(Concept c) {
    long time = System.currentTimeMillis();
    addObject(c);
    long time2 = System.currentTimeMillis() - time;
    //System.out.println("temps d'execution : " + time2);
  }

  public void doAlgorithm() {
    //jobObserv.sendMessage("Incremental Algorithm is in progress!\n");
    long time = System.currentTimeMillis();
    doIncre(col);
//	petko test code 30-Avr-2004
//	AbstractCompleteConceptLattice lattice= getLattice();
//	Iterator it=lattice.iterator();
//	int counter=0;
//	while(it.hasNext())
//	{
//		counter++;
//		LatticeNode node = (LatticeNode)it.next();
//		Intent  intent=node.getConcept().getIntent();
//		String str=intent.toString();
//		System.out.println(str);
//	}
//	System.out.println(counter);    
    long time2 = System.currentTimeMillis() - time;
    //System.out.println("temps d'execution : " + time2);
  }

  public String getDescription() {
    return "Valtchev & al. incremental lattice update, version 2 (2003)";
  }

  public void doIncre(Vector col) {
    int size = col.size();
    int j = 1;
    Date date = new Date();
    System.out.println("Add the first object at " + date.toString() + "\n");
    for (int i = 0; i < size; i++) {
      if (i == j * 500) {
        System.out.println("Add the " + i + "th object" + " at ");
        j++;
        date = new Date();
        System.out.println(date.toString() + "\n");
      }
      addObject( (ConceptImp) col.get(i));
	  sendJobPercentage(i*100 / col.size()); // gestion de la progression
    }
    date = new Date();
    System.out.println("Finish the algorithm at " + date.toString());
    System.out.println("Number of concepts : " + getLattice().size());
  }

  private void iniLattice(Vector col, MatrixBinaryRelationBuilder br) {
  	ConceptNodeImp.resetNodeId();
	ConceptNode topNode = new ConceptNodeImp( (ConceptImp) col.get(0));
	if (generators) {
	  Jen jen = new Jen(getLattice());
	  jen.calculGenerateursNoeud(topNode);
	}
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
	  ConceptNode bottomNode = new ConceptNodeImp(bottom);
	  getLattice().setBottom(bottomNode);
	  getLattice().setUpperCover(topNode, bottomNode);
	  getLattice().add(bottomNode);
	  getLattice().incNbOfNodes();
	}
	else getLattice().setBottom(topNode);
	col.remove(0);
  }
  
  private Iterator preProcess() {
    TreeMap sliceLattice = new TreeMap();
    Iterator allConcepts;
    Vector candidate = new Vector();
    Hashtable dealedConcept = new Hashtable();
    Node<Concept> topNode = getLattice().getTop();
    candidate.add(topNode);
    while (!candidate.isEmpty()) {
      ConceptNode cand = (ConceptNode) candidate.get(0);
      if (dealedConcept.get(cand) != null) {
        candidate.remove(0);
        continue;
      }
      Integer intentLen = new Integer( ( (cand.getContent()).getIntent()).size());
      Vector intentNode = new Vector();
      if ( (intentNode = (Vector) sliceLattice.get(intentLen)) != null) {
        intentNode.add(cand);
      }
      else {
        intentNode = new Vector();
        intentNode.add(cand);
        sliceLattice.put(intentLen, intentNode);
      }
      dealedConcept.put(cand, "");
      List children = cand.getChildren();
      candidate.addAll(children);
      candidate.remove(0);
    }
    allConcepts = ( (Collection) sliceLattice.values()).iterator();
    return allConcepts;
  }

  private void addObject(Concept newConcept) {
    Vector allConcepts = new Vector();
    Hashtable modifier = new Hashtable();
    Vector modified = new Vector();
    Vector newConcepts = new Vector();
    Hashtable chiPlus = new Hashtable();
    Iterator iterNode = preProcess();
    while (iterNode.hasNext()) {
      Vector intentNode = (Vector) iterNode.next();
      int nodeSize = intentNode.size();
      for (int j = 0; j < nodeSize; j++) {
        ConceptNode firstNode = (ConceptNode) intentNode.get(j);
        ConceptImp firstConcept = (ConceptImp) firstNode.getContent();
        ConceptImp QC = funcQ(firstConcept, newConcept);
        ConceptNode cN = (ConceptNode) getNoeud(firstNode, QC);
        ConceptImp c1;
        if (cN == null)
          c1 = null;
        else
          c1 = (ConceptImp) cN.getContent();
        int lengQC = QC.getIntent().size();
        if (c1 == null) {
          if (lengQC == (firstConcept.getIntent()).size()) {
            Extent extentC = firstConcept.getExtent();
            extentC = QC.getExtent();
            firstConcept.setExtent(extentC);
            ( (ConceptNodeImp) firstNode).concept = firstConcept;
            modifier.put(extentC, firstNode);
            modified.add(firstNode);
            chiPlus.put(firstNode, firstNode);
          }
          else {
            Extent extGenC = (Extent) funcQ(firstConcept, newConcept).getExtent().
                clone();
            Intent intGenC = (Intent) funcQ(firstConcept, newConcept).getIntent().
                clone();
            ConceptImp genC = new ConceptImp(extGenC, intGenC);
            ConceptNode genNode = new ConceptNodeImp(genC);
            cGen.put(genC, firstConcept);
            newConcepts.add(genNode);
            Vector minClo = minClosed(genC,
                                      minCandidate(uppCover(firstNode), chiPlus));
            int size = minClo.size();
            for (int i = 0; i < size; i++) {
              ConceptNode coverNode = (ConceptNode) minClo.get(i);
              newLink(coverNode, genNode);
              if (modifier.get( (coverNode.getContent()).getExtent()) != null) {
                dropLink(coverNode, firstNode);
              }
            }
            newLink(genNode, firstNode);
            if (firstNode == getLattice().getTop()) {
              getLattice().setTop(genNode);
            }
            getLattice().add(genNode);
            getLattice().incNbOfNodes();
            chiPlus.put(firstNode, genNode);

            if (generators) {
              // Calcul des générateurs
              if (firstNode.getChildren().isEmpty() &&
                  firstNode.getContent().getExtent().size() == 0) {
                Jen jen = new Jen(getLattice());
                jen.calculGenerateursNoeud(genNode);
              }
              else {
                ValtchevAlOnlineGeneratorUpdate.computeGenerators(firstConcept, genC);
              }
            }
          }
        }
        else {
          chiPlus.put(firstNode, chiPlus.get(cN));
        }

      }
    }
  }

  private Vector uppCover(ConceptNode node) {
    Vector upp = new Vector();
    upp.addAll(node.getParents());
    return upp;
  }

  private ConceptNode getNoeud(ConceptNode c, ConceptImp q) {
    ConceptNode nCour;
    if (c.getParents().size() == 0) {
      return null;
    }
    Iterator itU = c.getParents().iterator();
    while (itU.hasNext()) {
      ConceptNode upperCover = (ConceptNode) itU.next();
      ConceptImp upp = (ConceptImp) upperCover.getContent();
      int cur = this.funcQ(upp, q).getIntent().size();
      if (cur == q.getIntent().size()) {
        return (ConceptNode) upperCover;
      }
    }
    return null;
  }

  private ConceptNode argMax(Vector upp, ConceptImp newConcept) {
    ConceptNode max = null;
    if (upp.isEmpty())
      return max;
    int intentLength = funcQ( (ConceptImp) ( (ConceptNode) upp.get(0)).getContent(), newConcept).
        getIntent().size();
    max = (ConceptNode) upp.get(0);
    int size = upp.size();
    for (int i = 1; i < size; i++) {
      int uppLength = funcQ( (ConceptImp) ( (ConceptNode) upp.get(i)).getContent(), newConcept).
          getIntent().size();
      if (uppLength > intentLength) {
        intentLength = uppLength;
        max = (ConceptNode) upp.get(i);
      }
    }
    return max;
  }

  private ConceptImp funcQ(Concept firstConcept, Concept newConcept) {
    Intent cBarI = (firstConcept.getIntent()).intentIntersection(newConcept.getIntent());
    Extent cBarE = (firstConcept.getExtent()).extentUnion(newConcept.getExtent());
    ConceptImp cBar = new ConceptImp(cBarE, cBarI);
    return cBar;
  }

  private Vector minCandidate(Vector upp, Hashtable chiPlus) {
    Vector candidate = new Vector();
    TreeMap sliceCand = new TreeMap();
    int size = upp.size();
    for (int i = 0; i < size; i++) {
      ConceptNode node = (ConceptNode) chiPlus.get( (ConceptNode) upp.get(i));
      if (node != null) {
        Integer intentLen = new Integer( ( (node.getContent().getExtent()).size()));
        Vector sortCand = new Vector();
        if ( (sortCand = (Vector) sliceCand.get(intentLen)) != null) {
          sortCand.add(node);
        }
        else {
          sortCand = new Vector();
          sortCand.add(node);
          sliceCand.put(intentLen, sortCand);
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

  private Vector minClosed(ConceptImp first, Vector candidate) {
    Vector minClo = new Vector();
    Extent firstExtent = first.getExtent();
    Extent face = (Extent) (firstExtent.clone());
    int size = candidate.size();
    for (int i = 0; i < size; i++) {
      ConceptImp conCBar = (ConceptImp) ( (ConceptNode) candidate.get(i)).getContent();
      Extent extCBar = conCBar.getExtent();
      if ( (firstExtent.toString()).equals( (face.extentIntersection(extCBar)).
                                           toString())) {
        minClo.add( (ConceptNode) (candidate.get(i)));
        face = face.extentUnion(extCBar);
      }
    }
    return minClo;
  }

  private void newLink(ConceptNode node, ConceptNode childNode) {
    getLattice().setUpperCover(node, childNode);
  }

  private void dropLink(ConceptNode node, ConceptNode childNode) {
    childNode.removeParent(node);
    node.removeChild(childNode);
  }
}