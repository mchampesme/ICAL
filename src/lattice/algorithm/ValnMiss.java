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

package lattice.algorithm;

import java.util.Collection;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.Vector;

import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.Intent;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLatticeImp;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;

/**
 * 	DEAD CODE
 *
 * <p>Titre : Lattice</p>
 * <p>Description : Manipulation des treillis DEAD CODE</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : Université de Montréal</p>
 * @author Alexandre Frantz et Pascal Camarda
 * @version 1.0
 */
public class ValnMiss extends LatticeAlgorithmInc
{

 	/**
	 *
	 */
	public ValnMiss(MatrixBinaryRelationBuilder br) {
		super(br);
	}

   /**
   * Valtchev et Missaoui. (pas bon)
   * @param candidates
   * @param new_intent
   * @return
   */
  protected ConceptNodeImp isAGenerator2(Vector[] candidates, Intent new_intent)
  {
    if(candidates[new_intent.size()].isEmpty())
    {
      return null;
    }
    else
    {
      return (ConceptNodeImp)candidates[new_intent.size()].elementAt(0);
    }
  }

  /**
   * Valtchev et Missaoui (bon)
   * @param psi
   * @param new_intent
   * @param current_node
   * @return
   */
  protected ConceptNodeImp isAGenerator3(ConceptNodeImp[] psi, Intent new_intent,ConceptNodeImp current_node)
  {
    int size= new_intent.size();
    ConceptNodeImp candidate;

    for (Iterator i = current_node.parents.iterator(); i.hasNext();)
    {
      candidate = psi[( (ConceptNodeImp) i.next() ).id.intValue()];
      if(candidate.concept.getIntent().size()== size) return candidate;
    }
    return null;
  }

  /**
   * (Valtchev et Missaoui )findUpperCovers en utilisant les extents
   * @param candidates
   * @param current_node
   * @param new_node
   */
  protected void findUpperCovers( Vector[] candidates,
                                  ConceptNodeImp current_node,
                                  ConceptNodeImp new_node)
  {
    ConceptNodeImp parent;

    Vector true_covers = minima(candidates, new_node, current_node);

    for (Enumeration e = true_covers.elements(); e.hasMoreElements() ;)
    {
      parent = (ConceptNodeImp)e.nextElement();

      new_node.parents.add(parent);
      parent.children.add(new_node);

      // drop a link.
      if(current_node.parents.contains(parent))
      {
        current_node.parents.remove(parent);
        parent.children.remove(current_node);
      }
    }

    current_node.parents.add(new_node);
    new_node.children.add(current_node);
  }

  /**
   * (Valtchev et Missaoui) findUpperCovers en utilisant les intents.
   * @param candidates
   * @param current_node
   * @param new_node
   */
  protected void findUpperCovers3(Vector[] candidates,ConceptNodeImp current_node,
                                  ConceptNodeImp new_node)
  {
    ConceptNodeImp parent;

    Vector true_covers = minima3(candidates, new_node, current_node);
    // minima avec intent.

    int size = true_covers.size();

    // lier les noeuds ensemble (le nouveau noeud avec ses parents).
    for(int i = 0; i < size; i++)
    {
      parent = (ConceptNodeImp) true_covers.elementAt(i);
      new_node.parents.add(parent);
      parent.children.add(new_node);

      // drop a link.
      if(current_node.parents.contains(parent))
      {
        current_node.parents.remove(parent);
        parent.children.remove(current_node);
      }
    }
    // le generateur est l'enfant du nouveau noeud.
    current_node.parents.add(new_node);
    new_node.children.add(current_node);
  }

  /**
   * (Valtchev et Missaoui) minima avec Extent.
   * @param candidates
   * @param new_node
   * @param current_node
   * @return
   */
  protected Vector minima(Vector[] candidates, ConceptNodeImp new_node,
                          ConceptNodeImp current_node)
  {
    Vector trueCovers = new Vector();
    Extent knownExtent, current_extent;
    knownExtent = current_node.concept.getExtent().extentUnion(new_node.concept.getExtent());//replace by clone().
    for(int i=candidates.length-1; i>=0; i--)
    {
      for(int j=0; j<candidates[i].size(); j++)
      {
        if((((ConceptNodeImp)candidates[i].elementAt(j)).concept.getExtent().extentIntersection(knownExtent)).equals(new_node.concept.getExtent()))
        {
          knownExtent.addAll(((ConceptNodeImp)candidates[i].elementAt(j)).concept.getExtent());
          trueCovers.add(candidates[i].elementAt(j));
        }
      }
    }
    return trueCovers;
  }

  /**
   * (Valtchev et Missaoui) minima avec Intent.
   * @param candidates
   * @param new_node
   * @param current_node
   * @return
   */
  protected Vector minima3(Vector[] candidates, ConceptNodeImp new_node,
                           ConceptNodeImp current_node)
  {
    Vector trueCovers = new Vector();
    ConceptNodeImp node;
    int i;

    // Les candidats avec la plus grande cardinalitÈ d'intent sont Èlus d'office.
    for(i=candidates.length-1; i>=0; i--)
    {
      if(!candidates[i].isEmpty())
      {
        trueCovers.addAll(candidates[i]);
        break;
      }
    }

    // identifier le reste des Upper-covers.
    for(i=i-1; i>=0; i--)
    {
      for(int j=0; j<candidates[i].size(); j++)
      {
        node = (ConceptNodeImp)candidates[i].elementAt(j);
        if(isAMinima(trueCovers,node))
        {
          trueCovers.add(node);
        }
      }
    }
    return trueCovers;
  }

  /**
   * (Valtchev et Missaoui)
   * @param trueCovers
   * @param node
   * @return
   */
  protected boolean isAMinima(Vector trueCovers, ConceptNodeImp node)
  {
    for(int i = 0; i < trueCovers.size(); i++)
    {
      // le noeud est inclus dans un des candidats deja prÈsents.
      if(((ConceptNodeImp)trueCovers.elementAt(i)).concept.getIntent().containsAll(
                   node.concept.getIntent()))
      {
        return false;
      }
    }
    return true; // Le noeud est un Upper-Cover.
  }

  public void doAlgorithm() {
		ConceptNodeImp.resetNodeId();
		addAll_VM_Ext(getBinaryRelation().getInitialObjectPreConcept(MatrixBinaryRelationBuilder.NO_SORT));
        getBinaryRelation().setLattice(getLattice());
	}

/**
   *
   * @param coll
   */
  public void addAll_VM_Ext(Collection coll)
  {
    // --- Gestion de la progression
	int maxClass=coll.size();
	int nbClass = 0;
	// --- Fin Gestion de la progression
		

    for(Iterator iter = coll.iterator(); iter.hasNext() ;){
        addObjectExt((ConceptImp)iter.next());
        
        // --- Gestion de la progression
		nbClass++;
		//setPercentageOfWork(nbClass*100/maxClass);
		// --- Fin Gestion de la progression

    }
  }

  /**
   * add a collection of concepts to this lattice. (Godin-Ameliore Intent)
   * @param coll
   */
  public void addAll_VM_Int(Collection coll)
  {
    for(Iterator iter = coll.iterator(); iter.hasNext() ;)
    {
      addObjectInt((ConceptImp)iter.next());
    }
  }

  /**
   *
   * @param element
   */
  public void addObjectExt(Concept element)
  {
    if(getLattice().getBottom() == null)
    {
      ConceptNode n = new ConceptNodeImp(element);
      getLattice().setTop(n);
      getLattice().setBottom(n);

      getLattice().initialiseIntentLevelIndex(element.getIntent().size()+1);
      getLattice().set_max_transaction_size(element.getIntent().size());
      getLattice().addBottomToIntentLevelIndex(getLattice().getBottom());
      getLattice().incNbOfNodes();
    }

    else
    {
   adjustBottom((CompleteConceptLatticeImp)getLattice(),element);

      int max_intent_card = getLattice().getIntentLevelIndex().size();
      int nbr_element;
      Intent new_intent;
      ConceptImp new_concept;
      ConceptNodeImp current_node, new_node;
      Vector [] candidates;
      ConceptNodeImp[] psi = new ConceptNodeImp[ConceptNodeImp.next_id];

      //Treat each concept in ascending cardinality order.
      for(int i=0; i<max_intent_card;i++)
      {
        nbr_element = ((Vector) getLattice().getIntentLevelIndex().get(i)).size();
        for(int j=0; j<nbr_element; j++)
        {
          current_node = (ConceptNodeImp)((Vector) getLattice().getIntentLevelIndex().get(i)).elementAt(j);
          // modified node.
          if (isAModifiedNode(element, current_node))
          {
            current_node.concept.getExtent().addAll(element.getExtent());
            psi[current_node.id.intValue()]=current_node;
            if(current_node.concept.getIntent().equals(element.getIntent()))
            {
              getLattice().setTop(getLattice().findTop());
              return;
            }
          }

          // old pair
          else
          {
            new_intent = current_node.concept.getIntent().intentIntersection(element.getIntent());
            candidates =  candidates(current_node, psi);
            // current_node is a generator.
            if((new_node=isAGenerator2(candidates, new_intent))==null)
            {
              new_concept = new ConceptImp(current_node.concept.getExtent().extentUnion(element.getExtent()), new_intent);
              new_node = new ConceptNodeImp(new_concept);
              getLattice().add(new_node);
              findUpperCovers(candidates,current_node, new_node);
              getLattice().incNbOfNodes();
              if(new_intent.equals(element.getIntent()))
              {
                getLattice().setTop(getLattice().findTop());
                return;
              }
            }
            psi[current_node.id.intValue()]=new_node;
          }
        }
      }
      getLattice().setTop(getLattice().findTop());
    }
  }

  /**
   * Godin ameliorÈ (maxima avec intent).
   * @param element
   */
  public void addObjectInt(ConceptImp element)
  {
    if(getLattice().getBottom() == null)
    {
      ConceptNode n = new ConceptNodeImp(element);
      getLattice().setTop(n);
      getLattice().setBottom(n);
      getLattice().add(getLattice().getBottom());
      getLattice().incNbOfNodes();
    }
    else
    {
   adjustBottom((CompleteConceptLatticeImp)getLattice(),element);

      int max_intent_card = getLattice().getIntentLevelIndex().size();
      int nbr_element;
      Intent new_intent;
      ConceptImp new_concept;
      ConceptNodeImp current_node, new_node;
      Vector [] candidates;

      ConceptNodeImp[] psi =	new ConceptNodeImp[ConceptNodeImp.next_id];

      //Treat each concept in ascending cardinality order.
      for(int i=0; i<max_intent_card;i++)
      {
        nbr_element = getLattice().getIntentLevelIndex().get(i).size();

        for(int j=0; j<nbr_element; j++)
        {
          current_node = (ConceptNodeImp)
                         getLattice().getIntentLevelIndex().get(i).get(j);

          new_intent =
                  current_node.concept.getIntent().intentIntersection(element.getIntent());

          // if (isAMofiedNode(element, current_node)){  // modified node.
          if(new_intent.size()==current_node.concept.getIntent().size())
          {
            current_node.concept.getExtent().addAll(element.getExtent());

            psi[current_node.id.intValue()]=current_node;

            if(current_node.concept.getIntent().equals(element.getIntent()))
            {
              getLattice().setTop(getLattice().findTop());
              return;
            }
          }

          // old pair
          else
          {
            if((new_node=isAGenerator3(psi, new_intent, current_node))==null)
            {
              // current_node is a generator.
              new_concept =
                    new ConceptImp(current_node.concept.getExtent().extentUnion(
                                element.getExtent()), new_intent);

              new_node = new ConceptNodeImp(new_concept);

              getLattice().add(new_node);
              candidates = candidates(current_node, psi);
              findUpperCovers3(candidates,current_node, new_node);

              getLattice().incNbOfNodes();

              if(new_intent.equals(element.getIntent()))
              {
                getLattice().setTop(getLattice().findTop());
                return;
              }
            }

            psi[current_node.id.intValue()]=new_node;
          }
        }
      }
      getLattice().setTop(getLattice().findTop());
    }
  }
  
	public String getDescription(){
		return "ValnMiss incremental lattice update"; 
	}

	/* (non-Javadoc)
	 * @see lattice.algorithm.LatticeAlgorithmInc#addConcept(lattice.util.ConceptImp)
	 */
	public void addConcept(Concept c) {
		// TODO Auto-generated method stub
		
	}



}
