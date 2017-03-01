/*
 *  Copyright LIPN
 *  contributor(s) : Marc Champesme (2006) marc.champesme@lipn.univ-paris13.fr
 *  
 *  This software is a computer program whose purpose is the Incremental construction of Alpha lattices.
 *  
 *  This software is governed by the CeCILL license under French law and
 *  abiding by the rules of distribution of free software.  You can  use, 
 *  modify and/ or redistribute the software under the terms of the CeCILL
 *  license as circulated by CEA, CNRS and INRIA at the following URL
 *  "http://www.cecill.info". 
 *  
 *  As a counterpart to the access to the source code and  rights to copy,
 *  modify and redistribute granted by the license, users are provided only
 *  with a limited warranty  and the software's author,  the holder of the
 *  economic rights,  and the successive licensors  have only  limited
 *  liability. 
 *  
 *  In this respect, the user's attention is drawn to the risks associated
 *  with loading,  using,  modifying and/or developing or reproducing the
 *  software by the user in light of its specific status of free software,
 *  that may mean  that it is complicated to manipulate,  and  that  also
 *  therefore means  that it is reserved for developers  and  experienced
 *  professionals having in-depth computer knowledge. Users are therefore
 *  encouraged to load and test the software's suitability as regards their
 *  requirements in conditions enabling the security of their systems and/or 
 *  data to be ensured and,  more generally, to use and operate it in the 
 *  same conditions as regards security. 
 *  
 *  The fact that you are presently reading this means that you have had
 *  knowledge of the CeCILL license and that you accept its terms.
 */
package lattice.alpha.util;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import lattice.util.structure.Node;

/**
 *  Representation of immutable couples of Concept through ConceptNode suited to
 *  be used as key in a Map: hashCode and equals are defined according to this
 *  use. This representation make the hypothesis that the Concept inside the
 *  ConceptNode does not change during lifetime of a CoupleOfNodes instance.
 *  Changes made to the Node part of the ConceptNode that does not change the
 *  Concept part are ignored. Methods hashCode and equals only take into account
 *  the concepts underlying the ConceptNode.
 *
 * @author     Marc Champesme
 * @since      1 avr. 2005
 * @version    19 juin 2005
 */
public class CoupleOfNodes<E> extends Couple<Node<E>, Node<E>> {
	/*@
	  @ public model Concept firstConcept;
	  @ private represents firstConcept <- node1.getConcept();
	  @ public model Concept secondConcept;
	  @ private represents secondConcept <- node2.getConcept();
	  @
	  @ public invariant getNode1() != null && getNode2() != null;
	  @ public invariant firstConcept != null && secondConcept != null;
	  @ public invariant getNode1().getConcept().equals(firstConcept);
	  @ public invariant getNode2().getConcept().equals(secondConcept);
	  @ public constraint getNode1() == \old(getNode1());
	  @ public constraint getNode2() == \old(getNode2());
	  @ public constraint firstConcept.equals(\old(firstConcept));
	  @ public constraint secondConcept.equals(\old(secondConcept));
	  @
	  @*/

	private int hashCode;


	/**
	 *  Initialize a CoupleOfNodes object with the specified nodes.
	 *
	 * @param  node1  The first node of this couple
	 * @param  node2  The second node of this couple
	 */
	/*@
	  @ requires node1 != null && node2 != null;
	  @ requires node1.getConcept() != null;
	  @ requires node2.getConcept() != null;
	  @ ensures getNode1() == node1 && getNode2() == node2;
	  @
	  @*/
	public CoupleOfNodes(Node<E> node1, Node<E> node2) {
        super(node1, node2);
		computeHashCode();
	}


	/**
	 *  Compute ant return a list of all CoupleOfNodes made of one node of this
	 *  CoupleOfNodes, the other node being a parent node of the other node of this
	 *  CoupleOfNodes.
	 *
	 * @return    A list of CoupleOfNodes
	 */
	/*@
	  @ old Set node1Parents = getNode1().getParents();
	  @ old Set node2Parents = getNode2().getParents();
	  @ requires node1Parents != null;
	  @ requires node2Parents != null;
	  @ ensures \fresh(\result);
	  @ ensures \result.size() == node1Parents.size() + node2Parents.size();
	  @ ensures (\forall Object obj; \result.contains(obj);
	  @					obj instanceof CoupleOfNodes);
	  @ ensures (\forall CoupleOfNodes couple; \result.contains(couple);
	  @				(couple.getNode1() == getNode1()
	  @				 && node2Parents.contains(couple.getNode2()))
	  @				|| (node1Parents.contains(couple.getNode1())
	  @				    && couple.getNode2() == getNode2()));
	  @
	  @ pure
	  @*/
	public List<CoupleOfNodes<E>> upperCovers() {
        Set<Node<E>> node2Parents = second().getParents();
        Set<Node<E>> node1Parents = first().getParents();
		List<CoupleOfNodes<E>> resList = new ArrayList<CoupleOfNodes<E>>(node1Parents.size() + node2Parents.size());
		CoupleOfNodes<E> couple;

        for (Node<E> parent1 : node1Parents) {
			couple = new CoupleOfNodes<E>(parent1, second());
			resList.add(couple);
		}

        for (Node<E> parent2 : node2Parents) {
			couple = new CoupleOfNodes<E>(first(), parent2);
			resList.add(couple);
		}
		return resList;
	}


	/**
	 *  Test whether this CoupleOfNodes is equal to the given argument. This
	 *  CoupleOfNodes is equal to the given argument if the argument is a
	 *  CoupleOfNodes whose concepts are equals.
	 *
	 * @param  obj  The object to compare with this object.
	 * @return      Return true if the argument is a CoupleOfNodes corresponding to
	 *      an equal couple of ConceptNode ; else return false
	 */
	/*@ also
	  @	requires !(obj instanceof CoupleOfNodes);
	  @	ensures !\result;
	  @ also
	  @	requires obj instanceof CoupleOfNodes;
	  @	ensures \result <==> (firstConcept.equals(((CoupleOfNodes) obj).firstConcept)
	  @			      && secondConcept.equals(((CoupleOfNodes) obj).secondConcept));
	  @ also
	  @	ensures \result ==> hashCode() == ((CoupleOfNodes) obj).hashCode();
	  @
	  @ pure
	  @*/
	public boolean equals(Object obj) {
		if (!(obj instanceof CoupleOfNodes<?>)) {
			return false;
		}
		CoupleOfNodes<?> couple = (CoupleOfNodes<?>) obj;
		return first().getContent().equals(((Node<?>) couple.first()).getContent())
				 && second().getContent()
				.equals(((Node<?>) couple.second()).getContent());
	}


	/**
	 *  Compute and return the hashCode value of this CoupleOfNodes. This helper
	 *  method avoids to recompute the hashCode at each call to hashCode whereas
	 *  data used for this computation does'nt change. <p>
	 *
	 *  The value of the hashCode depends only of the intent and the extent of the
	 *  underlying concepts. </p>
	 */
	private void computeHashCode() {
		E c1 = first().getContent();
		E c2 = second().getContent();
		hashCode = c1.hashCode() * 31 + c2.hashCode();
	}


	/**
	 *  Return a hashcode for this CoupleOfNodes which depends only of the intents
	 *  and extents of the underlying concepts
	 *
	 * @return    A hashcode for this CoupleOfNodes
	 */
	/*@
	  @ pure
	  @*/
	public int hashCode() {
		return hashCode;
	}


	/**
	 *  Return a string representation of the two concepts corresponding to the two
	 *  nodes of this object.
	 *
	 * @return    a string representation of the two concepts corresponding to this
	 *      CoupleOfNodes
	 */
	//@ pure
	public String toString() {
		return first().getContent().toString() + " x "
				 + second().getContent().toString();
	}
}

