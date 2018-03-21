/*
 *********************************************************************** Copyright (C) 2004 The Galicia Team Modifications to the initial code base
 * are copyright of their respective authors, or their employers as appropriate.
 * Authorship of the modifications may be determined from the ChangeLog placed
 * at the end of this file. This program is free software; you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of the
 * License, or (at your option) any later version. This program is distributed
 * in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even
 * the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details. You should have
 * received a copy of the GNU Lesser General Public License along with this
 * program; if not, write to the Free Software Foundation, Inc., 59 Temple
 * Place, Suite 330, Boston, MA 02111-1307 USA; or visit the following url:
 * http://www.gnu.org/copyleft/lesser.html
 */

package lattice.util.structure;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Vector;

import lattice.util.concept.Concept;

/*
 * Description : Ajout de quelques m�thodes Copyright : Copyright (c) 2004
 * Soci�t� :Universite de Montr�al
 * @author Mame Awa Diop et Petko Valtchev
 * @version 1.1
 */

public class ConceptNodeImp implements ConceptNode {
    public static int next_id = 0;

    /**
    * 
    */
    public static void resetNodeId() {
        next_id = 0;
    }

    public static void setNodeId(int value) {
        next_id = value;
    }

    public Integer id;

    public boolean visited = false;

    public Concept concept; // element du noeud.

    public Set<Node<Concept>> parents;

    public List<Node<Concept>> children;

    // Pour les parcours en largeur
    private int degre = -1;

    /**
     * @param concept
     */
    public ConceptNodeImp(Concept concept) {
        this.concept = concept;
        parents = new HashSet<Node<Concept>>();
        children = new Vector<Node<Concept>>();
        id = new Integer(next_id);
        next_id = next_id + 1;
    }

    /**
     * Ce constructeur est appel� lors de la reconstitution du treillis.
     * 
     * @param id
     * @param concept
     */
    public ConceptNodeImp(Integer id, Concept concept) {
        this.concept = concept;
        parents = new HashSet<Node<Concept>>();
        children = new Vector<Node<Concept>>();
        this.id = id;

        if ((id.compareTo(new Integer(next_id)) > 0)
            || (id.compareTo(new Integer(next_id)) == 0)) {
            next_id = id.intValue() + 1;
        }
    }

    public void addChild(Node<Concept> N) {
        if (!children.contains(N))
            children.add(N);
    }

    public void addParent(Node<Concept> N) {
        if (!parents.contains(N))
            parents.add(N);
    }

    /*
     * (non-Javadoc)
     * @see lattice.util.Node#equals(lattice.util.Node)
     */
    public boolean equals(Object obj) {
        // by Amine
        if (!(obj instanceof Node<?>)) {
            return false;
        }
        Node<?> n = (Node<?>) obj;
        Object c = n.getContent();
        return getContent().equals(c);
    }

    /**
     * @return children
     */
    public List<Node<Concept>> getChildren() {
        return this.children;
    }

    /**
     * @return concept
     */
    public Concept getConcept() {
        return getContent();
    }

    /*
     * (non-Javadoc)
     * @see lattice.util.Node#getContent()
     */
    public Concept getContent() {
        return concept;
    }

    public int getDegre() {
        return degre;
    }

    // public boolean equals(Object o){
    // Concept c=((ConceptNode)o).getConcept();
    // return getConcept().equals(c);
    // }

    /**
     * @return id
     */
    public Integer getId() {
        return id;
    }

    /**
     * @return parents
     */
    public Set<Node<Concept>> getParents() {
        return this.parents;
    }

    /**
     * @return boolean value
     */
    public boolean getVisited() {
        return visited;
    }

    public void linkToUpperCovers(Node<Concept> child) {
        addParent(child);
        child.addChild(this);
    }

    public void removeChild(Node<Concept> N) {
        children.remove(N);
    }

    // -------------------------------------------------
    // M�thodes retir�es de CompleteConceptLattice

    public void removeParent(Node<Concept> N) {
        parents.remove(N);
    }

    public void resetDegre() {
        degre = -1;
        for (Iterator it = getChildren().iterator(); it.hasNext();) {
            ((ConceptNode) it.next()).resetDegre();
        }
    }

    public void setDegre(int d) {
        degre = d;
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
    public String toString() {
        return String.valueOf(id);
    }

    // -----------------------------------------------------

}
