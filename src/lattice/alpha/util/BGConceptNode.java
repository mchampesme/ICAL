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
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import lattice.util.concept.Concept;
import lattice.util.concept.Extent;
import lattice.util.concept.Intent;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.Node;

/**
 * A better implementation of interface ConceptNode but almost compatible
 * with ConceptNodeImp implementation. Main differences are:
 * <ul>
 * <li>equals methods are defined in term of reference equality</li>
 * <li>unused or redondant method from interface Node throw UnsupportedOperationException</li>
 * </ul>
 * 
 * @see        lattice.util.structure.ConceptNode
 * @see        lattice.util.structure.ConceptNodeImp
 * 
 * @author Mame Awa Diop and Petko Valtchev (for ConceptNodeImp implementation)
 * @author Marc Champesme (for this implementation)
 * @since      1 juillet 2005 
 * @version    7 juillet 2005
 */

public class BGConceptNode implements ConceptNode {
    /** 
     * Pour les parcours en largeur
     * 
     */
    private int degre = -1;
    
    private Integer id;

    private boolean visited = false;

    private Concept concept; // element du noeud.

    private Set<Node<Concept>> parents;

    private List<Node<Concept>> children;

    private static int next_id = 0;

    /**
     * 
     */
    public static void resetNodeId() {
        next_id = 0;
    }

    public static void setNodeId(int value) {
        next_id = value;
    }

 
    /**
     * Initialize a new node with the specified concept as content. 
     * This new node has no parents and no children
     * 
     * @param concept The concept to associate to this node
     */
    /*@
      @ requires concept != null;
      @ ensures getConcept() == concept;
      @ ensures getParents().isEmpty();
      @ ensures getChildren().isEmpty();
      @ ensures \fresh(getId());
      @*/
    public BGConceptNode(Concept concept) {
        this.concept = concept;
        parents = new HashSet<Node<Concept>>();
        children = new ArrayList<Node<Concept>>();
        id = new Integer(next_id);
        next_id = next_id + 1;
    }
    
     /**
      * Initialize a new node associated with a concept 
      * having the specified intent and extent
     * @param extent the extent of the concept associated to this node
     * @param intent the extent of the concept associated to this node
     */
    /*@
    @ requires extent != null && intent != null;
    @ ensures getConcept().getExtent().equals(extent);
    @ ensures getConcept().getIntent().equals(intent);
    @ ensures getParents().isEmpty();
    @ ensures getChildren().isEmpty();
    @ ensures \fresh(getId());
    @*/
    public BGConceptNode(Extent extent, Intent intent) {
        this(new BGConcept(extent, intent));
    }

    /**
     * Initialize a new node with the specified concept as content
     * and the specified id. 
     * This new node has no parents and no children
     * 
     * @param id The identifier to use for this node
     * @param concept The concept to associate to this node
     */
    /*@
      @ requires concept != null;
      @ ensures getConcept() == concept;
      @ ensures getParents().isEmpty();
      @ ensures getChildren().isEmpty();
      @ ensures getId() == id;
      @*/
    public BGConceptNode(Integer id, Concept concept) {
        this.concept = concept;
        parents = new HashSet<Node<Concept>>();
        children = new ArrayList<Node<Concept>>();
        this.id = id;

        if (id.compareTo(new Integer(next_id)) >= 0) {
            next_id = id.intValue() + 1;
        }
    }

    /**
     * @return concept
     */
    /*@ also
      @ ensures \result != null;
      @ pure
      @*/
    public Concept getContent() {
        return concept;
    }

    /**
     * Returns an identifier for this node. This identifier is mainly
     * intended for debugging or lattice presentation purpose.
     * @return an identifier for this node.
     */
    /*@
      @ pure
      @*/
    public Integer getId() {
        return id;
    }

    /**
     * @return parents
     */
    /*@
    @ pure
    @*/
    public Set<Node<Concept>> getParents() {
        return this.parents;
    }

    public void addParent(Node<Concept> node) {
        parents.add(node);
    }

    public void removeParent(Node<Concept> node) {
        parents.remove(node);
    }

    /**
     * @return children
     */
    /*@
      @ pure
      @*/
    public List<Node<Concept>> getChildren() {
        return this.children;
    }
    
    public void addChild(Node<Concept> node) {
        if (!children.contains(node))
            children.add(node);
    }
    
    public void removeChild(Node<Concept> node) {
        children.remove(node);
    }
    
    /**
     * @return boolean value
     */
    /*@
      @ pure
      @*/
    public boolean getVisited() {
        return visited;
    }
    
    /**
     * @param b
     */
    public void setVisited(boolean b) {
        this.visited = b;
    }
    
    /**
     * @return a string representation of this latticeNode
     */
    /*@
      @ pure
      @*/
    public String toString() {
        return String.valueOf(id);
    }

    public void setDegre(int d) {
        degre = d;
    }

    public int getDegre() {
        return degre;
    }

    public void resetDegre() {
        degre = -1;
        for (Iterator<Node<Concept>> it = getChildren().iterator(); it.hasNext();) {
            ((BGConceptNode) it.next()).resetDegre();
        }
    }

    // -------------------------------------------------
    // M�thodes retir�es de CompleteConceptLattice

    /**
     * Adds the specified node to the parents of this node and adds this node to
     * the children of the specified node. 
     * 
     * @param parent
     *            a parent node of this node
     * @see lattice.util.structure.ConceptNode#linkNodeToUpperCovers(lattice.util.structure.ConceptNode)
     */
    public void linkToUpperCovers(Node<Concept> parent) {
        addParent(parent);
        parent.addChild(this);
    }

}
