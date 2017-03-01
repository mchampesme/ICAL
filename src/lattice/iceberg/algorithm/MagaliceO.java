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

import java.util.Collection;
import java.util.Comparator;
import java.util.Date;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Vector;

import lattice.algorithm.LatticeAlgorithm;
import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
import lattice.util.structure.Node;
import rule.generator.Jen;
import rule.generator.ValtchevAlOnlineGeneratorUpdate;

/**
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public final class MagaliceO
    extends LatticeAlgorithm {

  public Extent ext = new SetExtent();
  public Hashtable contextIndex = new Hashtable();
  public HashSet modifiedSet = new HashSet();
  public Set dropedNode = new HashSet();
  public Hashtable SEen = new Hashtable();
  public Hashtable Jumper = new Hashtable();
  public int nbObj;
  public int nbAtt;
  public int nbNodes;
  public TreeMap CndJumper = new TreeMap(new sizeCompare());
  public Set visitedNode = new HashSet();
  public Set visited = new HashSet();
  private boolean generators = false;

//-------------------------------------------------------------/
  // constructors
  /**
   * Constructor Magalice.
   * @param binaryRelation
   *
   *
   */

  private Vector col;

  public double minSupport = 0.03;
  Intent intent = null;
  Extent extent = null;

  public MagaliceO(MatrixBinaryRelationBuilder br, double minSupp) {
    super(br);
    this.minSupport = minSupp;

    Date date = new Date();

    System.out.println("Begin Construct ini concept from " + date.toString());

    col = (Vector) br.getInitialObjectPreConcept(MatrixBinaryRelationBuilder.NO_SORT);

    intent = ( (ConceptImp) col.get(0)).getIntent();
    extent = ( (ConceptImp) col.get(0)).getExtent();
    setContextIndex(extent, intent);

    date = new Date();

    System.out.println("End Construct ini concept at " + date.toString());

    if (!col.isEmpty()) {

      date = new Date();

      System.out.println("Begin initialization from " + date.toString());

      iniLattice(col, br);
      nbObj = nbObj + 1;

      date = new Date();

      System.out.println("End initialization at " + date.toString());
    }

  }

  public MagaliceO(MatrixBinaryRelationBuilder br, double minSupp, boolean gens) {
    super(br);
    this.minSupport = minSupp;
    this.generators = gens;
    Date date = new Date();

    System.out.println("Begin Construct ini concept from " + date.toString());

    col = (Vector) br.getInitialObjectPreConcept(MatrixBinaryRelationBuilder.NO_SORT);

    intent = ( (ConceptImp) col.get(0)).getIntent();
    extent = ( (ConceptImp) col.get(0)).getExtent();
    setContextIndex(extent, intent);

    date = new Date();

    System.out.println("End Construct ini concept at " + date.toString());

    if (!col.isEmpty()) {

      date = new Date();

      System.out.println("Begin initialization from " + date.toString());

      iniLattice(col, br);
      nbObj = nbObj + 1;

      date = new Date();

      System.out.println("End initialization at " + date.toString());
    }

  }

//-------------------------------------------------------------/
  public void execAlgo() {
    nbAtt = 0;
    nbObj = 1;
    nbNodes = 0;
    getLattice().incNbOfNodes();

    doIncre(col);

  }

  public void doAlgorithm() {
    if (jobObserv != null) jobObserv.setTitle(getDescription() +
                                              " in progress...\n");
    execAlgo();
    //jobObserv.sendMessage("Magalice is over!...\n");
  }

  public String getDescription() {

    return "Magalice incremental iceberg update";

  }

  public void doIncre(Vector col) {

    int size = col.size();

    int j = 1;

    Date date = new Date();

    System.out.println("Add the first object at " + date.toString() + "\n");

    for (int i = 0; i < size; i++) {

      nbObj = nbObj + 1;

      if (i == j * 100) {

        System.out.println("Add the " + i + "th object" + " at ");

        j++;

        date = new Date();

        System.out.println(date.toString() + "\n");

      }

      intent = ( (ConceptImp) col.get(i)).getIntent();
      extent = ( (ConceptImp) col.get(i)).getExtent();
      setContextIndex(extent, intent);
      SEen.clear();
      Jumper.clear();
      visitedNode.clear();
      dropedNode.clear();
      CndJumper.clear();

      addObject( (ConceptImp) col.get(i));

      crossIceberg(getLattice().getTop());

      Iterator itDrop = dropedNode.iterator();
      while (itDrop.hasNext()) {
        Node<Concept> dropConceptNode = (ConceptNodeImp) itDrop.next();
        drop(dropConceptNode);
      }

      Iterator itr = CndJumper.entrySet().iterator();
      while (itr.hasNext()) {
        Map.Entry entry = (Map.Entry) itr.next();
        HashSet hs = (HashSet) entry.getValue();
        Iterator is = hs.iterator();

        while (is.hasNext()) {
          Node<Concept> cn = (Node<Concept>) is.next();
          findLowerCovers(cn, intent, extent);
        }
      }
    }
    
    date=new Date();
	visited.clear();
	nbNodes++;
	countConceptNodes(getLattice().getTop());
	System.out.println("Number of concepts: "+nbNodes);
	System.out.println("Finish the algorithm at "+date.toString());    
    
  }

//-------------------------------------------------------------/
  private void iniLattice(Vector col, MatrixBinaryRelationBuilder br) {

  	ConceptNodeImp.resetNodeId();
  	Node<Concept> topConceptNode = new ConceptNodeImp( (ConceptImp) col.get(0));

    getLattice().setTop(topConceptNode);
    if (generators) {
      Jen jen = new Jen(getLattice());
      jen.calculGenerateursNoeud(topConceptNode);
    }
    getLattice().incNbOfNodes();

    getLattice().initialiseIntentLevelIndex(br.getAttributesNumber() + 1);

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

    }

    col.remove(0);

  }

//-------------------------------------------------------------/

  private Iterator preProcess() {

    TreeMap sliceLattice = new TreeMap();

    Iterator allConcepts;

    Vector candidate = new Vector();

    Hashtable dealedConcept = new Hashtable();

    Node<Concept> topConceptNode = getLattice().getTop();

    candidate.add(topConceptNode);

    while (!candidate.isEmpty()) {

      Node<Concept> cand = (Node<Concept>) candidate.get(0);

      if (dealedConcept.get(cand) != null) {

        candidate.remove(0);

        continue;

      }

      Integer intentLen = new Integer( ( (cand.getContent()).getIntent()).size());

      Vector intentConceptNode = new Vector();

      if ( (intentConceptNode = (Vector) sliceLattice.get(intentLen)) != null) {

        intentConceptNode.add(cand);

      }

      else {

        intentConceptNode = new Vector();

        intentConceptNode.add(cand);

        sliceLattice.put(intentLen, intentConceptNode);

      }

      dealedConcept.put(cand, "");

      List children = cand.getChildren();

      candidate.addAll(children);

      candidate.remove(0);

    }

    allConcepts = ( (Collection) sliceLattice.values()).iterator();

    return allConcepts;

  }

//-------------------------------------------------------------/

  private void addObject(ConceptImp newConcept) {

    Vector allConcepts = new Vector();

    Hashtable modifier = new Hashtable();

    Hashtable chiPlus = new Hashtable();

    Iterator iterConceptNode = preProcess();

    while (iterConceptNode.hasNext()) {

      Vector intentConceptNode = (Vector) iterConceptNode.next();

      int ConceptNodeSize = intentConceptNode.size();

      for (int j = 0; j < ConceptNodeSize; j++) {

        Node<Concept> firstConceptNode = (Node<Concept>) intentConceptNode.get(j);

        ConceptImp firstConcept =(ConceptImp) firstConceptNode.getContent();

        Vector upp = uppCover(firstConceptNode);

        Node<Concept> newMaxConceptNodeTemp = argMax(upp, newConcept);

        Node<Concept> newMaxConceptNode = null;

        if (newMaxConceptNodeTemp != null) {

          newMaxConceptNode = (Node<Concept>) chiPlus.get(newMaxConceptNodeTemp);
        }

        int lengC, lengNew;

        if (newMaxConceptNode == null) {

          lengNew = -1;
        }

        else {

          ConceptImp newMaxConcept = (ConceptImp) newMaxConceptNode.getContent();

          lengNew = funcQ(newMaxConcept, newConcept).size();

        }

        lengC = funcQ(firstConcept, newConcept).size();

        if (lengC != lengNew) {

          if (lengC == (firstConcept.getIntent()).size()) {

            Extent extentC = firstConcept.getExtent();

            extentC = extentC.extentUnion(newConcept.getExtent());

            firstConcept.setExtent(extentC);

            ( (ConceptNodeImp) firstConceptNode).concept = firstConcept;

            modifier.put(extentC, firstConceptNode);

            newMaxConceptNode = firstConceptNode;

            Integer ix = new Integer(firstConceptNode.getContent().getIntent().size());
            HashSet s = (HashSet) CndJumper.get(ix);
            if (s == null)
              s = new HashSet();
            s.add(firstConceptNode);
            CndJumper.put(ix, s);

          }

          else {

            Extent extGenC = (Extent) ( (firstConcept.getExtent()).extentUnion(
                newConcept.getExtent())).clone();

            ConceptImp genC = new ConceptImp(extGenC,
                                             (Intent) funcQ(firstConcept,
                newConcept).clone());

            Node<Concept> genConceptNode = new ConceptNodeImp(genC);

            Integer ix = new Integer(genConceptNode.getContent().getIntent().size());
            HashSet s = (HashSet) CndJumper.get(ix);
            if (s == null)
              s = new HashSet();
            s.add(genConceptNode);
            CndJumper.put(ix, s);

            Vector minClo = minClosed(genC, minCandidate(upp, chiPlus));

            int size = minClo.size();

            for (int i = 0; i < size; i++) {

              Node<Concept> coverConceptNode = (Node<Concept>) minClo.get(i);

              Iterator itChild = coverConceptNode.getChildren().iterator();
              boolean exist = false;
              while (itChild.hasNext() && exist == false) {
                Node<Concept> nChild = (ConceptNodeImp) itChild.next();
                if (nChild.getContent().getIntent().equals(genConceptNode.getContent().
                    getIntent()) == true)
                  exist = true;
              }
              if (exist == false)

                newLink(coverConceptNode, genConceptNode);

              if (modifier.get( (coverConceptNode.getContent()).getExtent()) != null) {

                dropLink(coverConceptNode, firstConceptNode);

              }

            }

            newLink(genConceptNode, firstConceptNode);

            if (firstConceptNode == getLattice().getTop()) {

              getLattice().setTop(genConceptNode);

            }

            if (generators) {
              // Calcul des générateurs
              if (firstConceptNode.getChildren().isEmpty() &&
                  firstConceptNode.getContent().getIntent().size() == nbAtt) {
                Jen jen = new Jen(getLattice());
                jen.calculGenerateursNoeud(genConceptNode);
              }
              else {
                ValtchevAlOnlineGeneratorUpdate.computeGenerators(firstConcept, genC);
              }
            }

            newMaxConceptNode = genConceptNode;

            getLattice().add(genConceptNode);

            getLattice().incNbOfNodes();

          }

        }

        chiPlus.put(firstConceptNode, newMaxConceptNode);

      }

    }

  }

//-------------------------------------------------------------/

  public Vector uppCover(Node<Concept> cnode) {

    Vector upp = new Vector();

    upp.addAll(cnode.getParents());

    return upp;
  }

//-------------------------------------------------------------/

  public Node<Concept> argMax(Vector upp, ConceptImp newConcept) {

    Node<Concept> max = null;

    if (upp.isEmpty())return max;

    int intentLength=funcQ((ConceptImp) ((Node<Concept>)upp.get(0)).getContent(),newConcept).size();
    
    max = (Node<Concept>) upp.get(0);

    int size = upp.size();

    for (int i = 1; i < size; i++) {

    	int uppLength=funcQ((ConceptImp) ((Node<Concept>)upp.get(i)).getContent(),newConcept).size();

      if (uppLength > intentLength) {

        intentLength = uppLength;

        max = (Node<Concept>) upp.get(i);

      }

    }

    return max;

  }

//-------------------------------------------------------------/

  public Intent funcQ(ConceptImp firstConcept, ConceptImp newConcept) {

    Intent cBar = (firstConcept.getIntent()).intentIntersection(newConcept.getIntent());

    return cBar;
  }

//-------------------------------------------------------------/

  public Vector minCandidate(Vector upp, Hashtable chiPlus) {

    Vector candidate = new Vector();

    TreeMap sliceCand = new TreeMap();

    int size = upp.size();

    for (int i = 0; i < size; i++) {

      Node<Concept> cnode = (Node<Concept>) chiPlus.get( (Node<Concept>) upp.get(i));

      if (cnode != null) {

        Integer intentLen = new Integer( ( (cnode.getContent().getExtent()).size()));

        Vector sortCand = new Vector();

        if ( (sortCand = (Vector) sliceCand.get(intentLen)) != null) {

          sortCand.add(cnode);

        }

        else {

          sortCand = new Vector();

          sortCand.add(cnode);

          sliceCand.put(intentLen, sortCand);

        }

      }

    }

    Iterator allCand = ( (Collection) sliceCand.values()).iterator();

    while (allCand.hasNext()) {

      Vector sortCand = (Vector) allCand.next();

      int ConceptNodeSize = sortCand.size();

      for (int j = 0; j < ConceptNodeSize; j++) {

        candidate.add( (Node<Concept>) sortCand.get(j));

      }

    }

    return candidate;

  }

//-------------------------------------------------------------/

  public Vector minClosed(ConceptImp first, Vector candidate) {

    Vector minClo = new Vector();

    Extent firstExtent = first.getExtent();

    Extent face = (Extent) (firstExtent.clone());

    int size = candidate.size();

    for (int i = 0; i < size; i++) {

      ConceptImp conCBar=(ConceptImp) ((Node<Concept>)candidate.get(i)).getContent();

      Extent extCBar = conCBar.getExtent();

      if ( (firstExtent.toString()).equals( (face.extentIntersection(extCBar)).
                                           toString())) {

        minClo.add( (Node<Concept>) (candidate.get(i)));

        face = face.extentUnion(extCBar);

      }

    }

    return minClo;

  }

//-------------------------------------------------------------/

  public void newLink(Node<Concept> cnode, Node<Concept> childConceptNode) {

    getLattice().setUpperCover(cnode, childConceptNode);

  }

//-------------------------------------------------------------/
  public void dropLink(Node<Concept> cnode, Node<Concept> childConceptNode) {

    childConceptNode.removeParent(cnode);

    cnode.removeChild(childConceptNode);

  }

//-------------------------------------------------------------/

  private void findLowerCovers(Node<Concept> cnode, Intent intent, Extent extent) {

    Hashtable Candidates = new Hashtable();
    Set ConceptNodeNewSeen = new TreeSet();
    Set Attrib = new TreeSet();

    if (!cnode.getChildren().isEmpty()) {
      Iterator itParent = cnode.getChildren().iterator();
      while (itParent.hasNext()) {
        Node<Concept> nPrt = (ConceptNodeImp) itParent.next();

        if (nPrt.getContent().getExtent().containsAll(extent)) {
          Set AttPrt = (Set) SEen.get(nPrt.getId());
          AttPrt.addAll(nPrt.getContent().getIntent());
          AttPrt.removeAll(cnode.getContent().getIntent());
          Attrib.addAll(AttPrt);
        }
      }
    }

    SEen.put(cnode.getId(), Attrib);

    Attrib = (Set) SEen.get(cnode.getId());
    Attrib.addAll(cnode.getContent().getIntent());
    Set candidates = new TreeSet();

    candidates = difr(cnvrt(intent), Attrib);
    Vector candidates1 = new Vector(candidates);

    while (!candidates1.isEmpty()) {
      FormalAttribute fa = (FormalAttribute) candidates1.get(0);
      Intent Int = getA(fa);
      Extent Ext = getExtent(Int);

      Extent e = null;
      e = cnode.getContent().getExtent().extentIntersection(Ext);

      int nObj = nbObj - 1;
      double k = (double) e.size();
      double bi = minSupport * nObj + minSupport;
      double bs = minSupport * nObj + 1;
      bi = round(bi, 2);
      bs = round(bs, 2);

      if ( (k < bs) && (k >= bi)) {
        Node<Concept> childConceptNode = (Node<Concept>) Jumper.get(e);
        if (childConceptNode != null) {
          childConceptNode.linkToUpperCovers(cnode);
          // Calcul des générateurs
          if (generators) {
            Jen jen = new Jen(getLattice());
            jen.calculGenerateursNoeud(childConceptNode);
          }
          ConceptNodeNewSeen.addAll(childConceptNode.getContent().getIntent());
          ConceptNodeNewSeen.removeAll(cnode.getContent().getIntent());
          candidates1.removeAll(childConceptNode.getContent().getIntent());
        }
        else {
          Intent iFound = (Intent) Candidates.get(e);
          if (iFound != null) {
            iFound.add(fa);
            Candidates.put(e, iFound);
          }
          else {
            Intent newInt = cnode.getContent().getIntent().intentUnion(Int);
            Candidates.put(e, newInt);
          }
          ConceptNodeNewSeen.add(fa);
        }
      }
      if (!candidates1.isEmpty())
        if (fa.equals(candidates1.get(0)))
          candidates1.remove(0);
    }

    Enumeration iter = Candidates.keys();
    Intent newInt = new SetIntent();
    Extent newExt = new SetExtent();
    while (iter.hasMoreElements()) {
      newExt = (Extent) iter.nextElement();
      newInt = (Intent) Candidates.get(newExt);
      ConceptImp c = new ConceptImp(newExt, newInt);
      Node<Concept> lowerConceptNode = new ConceptNodeImp(c);

      lowerConceptNode.linkToUpperCovers(cnode);
      if (generators) {
        // Calcul des générateurs
        Jen jen = new Jen(getLattice());
        jen.calculGenerateursNoeud(lowerConceptNode);
      }
      getLattice().incNbOfNodes();
      SEen.put(lowerConceptNode, new TreeSet());
      getLattice().add(lowerConceptNode);
      Jumper.put(newExt, lowerConceptNode);
    }
    Set ndSeen = new TreeSet();
    ndSeen = (TreeSet) SEen.get(cnode.getId());
    ndSeen.addAll(ConceptNodeNewSeen);
    SEen.put(cnode.getId(), ndSeen);
  }

//-------------------------------------------------------------/

  public Extent getExtent(Intent intent) {

    Iterator attributs = intent.iterator();
    FormalAttribute j = (FormalAttribute) attributs.next();
    Intent i = getA(j);
    Extent ex = (Extent) contextIndex.get(i);
    while (attributs.hasNext()) {
      j = (FormalAttribute) attributs.next();
      i = getA(j);
      Extent idObject = (Extent) contextIndex.get(i);
      ex.extentIntersection(idObject);
    }
    return (ex);
  }

//-------------------------------------------------------------/
  public Set difr(Set v1, Set v2) {
    Set v = v1;
    v.removeAll(v2);
    return (v);
  }

//-------------------------------------------------------------/
  public Vector difr(Vector v1, Vector v2) {
    Vector v = v1;
    v.removeAll(v2);
    return (v);
  }

//-------------------------------------------------------------/
  public void setContextIndex(Extent object, Intent intent) {
    Iterator attributs = intent.iterator();
    while (attributs.hasNext()) {
      FormalAttribute j = (FormalAttribute) attributs.next();
      Intent i = getA(j);
      Extent idObject = (Extent) contextIndex.get(i);
      if (idObject == null)
        idObject = new SetExtent();

      idObject = idObject.extentUnion(object);
      contextIndex.put(i, idObject);
    }
  }

//-------------------------------------------------------------/
  public void crossIceberg(Node<Concept> n) {
    double u = 0;

    if (visitedNode.contains(n) == false) {
      visitedNode.add(n);
      double a = n.getContent().getExtent().size();
      double b = nbObj;
      u = a / b;
      if (u < minSupport) {
        dropedNode.add(n);
        getLattice().remove(n);
      }
      else {
        Iterator itr = n.getChildren().iterator();
        while (itr.hasNext()) {
        	ConceptNodeImp parent = (ConceptNodeImp) itr.next();
        	crossIceberg(parent);
        }
      }
    }
  }

//-------------------------------------------------------------/
  public Set cnvrt(Intent intent) {
    Set v = new HashSet();
    Iterator it = intent.iterator();
    while (it.hasNext())
      v.add(it.next());
    return (v);
  }

  //-------------------------------------------------------------/
  public Vector convert(Intent intent) {
    Vector v = new Vector();
    Iterator it = intent.iterator();
    while (it.hasNext())
      v.add(it.next());
    return (v);
  }

//-------------------------------------------------------------/

  public double round(double val, int places) {
    long factor = (long) Math.pow(10, places);

    val = val * factor;

    long tmp = Math.round(val);

    return (double) tmp / factor;
  }

//-------------------------------------------------------------/

  static class sizeCompare
      implements Comparator {

    public int compare(Object o1, Object o2) {
      Integer i1 = (Integer) o1;
      Integer i2 = (Integer) o2;
      return (i2.intValue() - i1.intValue());
    }
  }

  //-------------------------------------------------------------/
  public void drop(Node<Concept> cnode) {

    Set l = cnode.getParents();
    Set v = new HashSet();
    v.addAll(l);

    Iterator it = v.iterator();
    while (it.hasNext()) {
      Node<Concept> ne = (Node<Concept>) it.next();
      drop(cnode, ne);
    }
  }

  //-------------------------------------------------------------/
  public void drop(Node<Concept> np, Node<Concept> nc) {
    np.getParents().remove(nc);
    nc.getChildren().remove(np);
  }

//-------------------------------------------------------------/
  public Intent getA(FormalAttribute a) {
    Intent intent = new SetIntent();
    intent.add(a);
    return intent;
  }

//-------------------------------------------------------------/
  public void countConceptNodes(Node<Concept> nod) {

    Iterator it = nod.getChildren().iterator();
    while (it.hasNext()) {
    	ConceptNodeImp pt = (ConceptNodeImp) it.next();
      if (!visited.contains(pt)) {
        visited.add(pt);
        nbNodes++;
        countConceptNodes(pt);
      }
    }
  }
//-------------------------------------------------------------/

} // of class
