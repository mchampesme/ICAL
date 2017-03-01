/*
 * **********************************************************************
 * Copyright (C) 2004 The Galicia Team Modifications to the initial code base
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
 * **********************************************************************
 */

package lattice.util.structure;

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import lattice.util.concept.Concept;
import lattice.util.index.LevelIndex;
import lattice.util.relation.RelationBuilder;

/**
 * <p>
 * Titre : Lattice
 * </p>
 * <p>
 * Description : Manipulation des treillis
 * </p>
 * <p>
 * Copyright : Copyright (c) 2002
 * </p>
 * <p>
 * Société : Université de Montréal
 * </p>
 * 
 * @author Alexandre Frantz et Pascal Camarda
 * @version 1.0
 */

/*
 * Title : Réingénierie du package util : Fusion de util et util2 Description :
 * Fusion de la classe LinkedConceptLattice (util) et de la classe
 * ConceptLattice (util2) Copyright: Copyright (c) 2004 Company: Universite de
 * Montréal
 * 
 * @version 1.1 @author Mame Awa Diop et Petko Valtchev TODO To change the
 *          template for this generated type comment go to Window - Preferences -
 *          Java - Code Style - Code Templates
 */

public class CompleteConceptLatticeImp extends AbstractCompleteConceptLattice {

    public LevelIndex intent_level_index; // Index des concepts par la taille

    // (cardinalité) de leur intention
    protected int max_transaction_size;

    protected int nbr_concept;

    /**
     *
     */
    public CompleteConceptLatticeImp() {
        top = null;
        bottom = null;
        intent_level_index = new LevelIndex();
        max_transaction_size = 0;
        setNbOfNodes(0);
    }

    // -----------------------------------------------------
    // Fusion util et util2 : le constructeur

    /**
     * Constructor for AbstractCompleteConceptLattice.
     * 
     * @param relation
     */
    public CompleteConceptLatticeImp(RelationBuilder relation) {
        super(relation);
    }

    // ---------------------------------------------------

    /**
     * @param node
     */
    public void add(Node<Concept> node) {
        intent_level_index.addNodeToIntentLevelIndex(node);
    }

    /**
     * @param node
     */
    public void addBottomToIntentLevelIndex(Node<Concept> node) {
        intent_level_index.addBottomToIntentLevelIndex(node);
    }

    /**
     * @return bottom
     */
    public Node<Concept> findBottom() {
        return (ConceptNodeImp) ((Vector) intent_level_index.lastElement())
                .firstElement();
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.util.structure.CompleteConceptLattice#findNode(java.lang.Integer)
     */
    // Added by Amine 16 august 2004 - 03:02 PM
    // purpose: reduction of redundant links in relational lattices
    public Node<Concept> findNode(Integer conceptNodeID) {
        Iterator<Node<Concept>> latticeIt = this.iterator();
        while (latticeIt.hasNext()) {
            Node<Concept> cn = latticeIt.next();
            if (cn.getId().equals(conceptNodeID))
                return cn;
        }
        return null;
    }

    public Node<Concept> findTop() {
        for (int i = 0; i < intent_level_index.size(); i++) {
            if (!(intent_level_index.isEmpty(i))) {
                return (Node<Concept>) intent_level_index.first(i);
            }
        }
        return null;
    }

    public Node<Concept> getNode(Concept c) {
        // TODO Auto-generated method stub
        return null;
    }

    /**
     * @return Vector
     */
    public List<List<Node<Concept>>> getIntentLevelIndex() {
        return intent_level_index.get_intent_level_index();
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.util.structure.CompleteConceptLattice#getMinSupp()
     */
    public double getMinSupp() {
        // TODO Auto-generated method stub
        return 0;
    }

    /**
     * Set number of concept + 1
     */
    public void incNbOfNodes() {
        this.nbr_concept += 1;
    }

    /**
     * Mettre a jour le vecteur intent_level_index.
     * 
     * @param size
     */
    public void initialiseIntentLevelIndex(int size) {
        intent_level_index.initialiseIntentLevelIndex(size);
    }

    /**
     * @return boolean
     */
    public boolean isEmpty() {
        return nbr_concept == 0;
    }

    /**
     * Iterator donne acces aux ÈlÈments du treillis par cardinalitÈ croissante
     * de leur intent. A garder.
     */
    public Iterator<Node<Concept>> iterator() {
        return new ConceptLatticeIterator(getIntentLevelIndex());
    }

    // /////////////// IMPLEMENTATION Algo Bordat////////////

    // -------------------------------------------------------------/
    public void linkToUpperCovers(Node<Concept> node, Node<Concept> child) {
        node.getParents().add(child);
        child.getChildren().add(node);
    }

    /**
     * @param node
     */
    public void remove(Node<Concept> node) {
        intent_level_index.removeNodeFromIntentLevelIndex(node);
    }

    /**
     * set max_transaction_size
     * 
     * @param m
     */
    public void set_max_transaction_size(int m) {
        this.max_transaction_size = m;
    }

    /**
     * @param b
     */
    public void setBottom(Node<Concept> b) {
        this.bottom = b;
    }


    /*
     * (non-Javadoc)
     * 
     * @see lattice.util.structure.CompleteConceptLattice#setMinSupp(double)
     */
    public void setMinSupp(double d) {
        // TODO Auto-generated method stub

    }

    /**
     * Set number of concept
     * 
     * @param n
     */
    public void setNbOfNodes(int n) {
        this.nbr_concept = n;
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.util.SupSemiLattice#setTop(lattice.util.Node)
     */
    public void setTop(Node<Concept> top) {
         this.top = top;
    }

    /**
     * @param node
     * @param enfant
     */
    public void setUpperCover(Node<Concept> node, Node<Concept> enfant) {
        node.getChildren().add(enfant);
        enfant.getParents().add(node);
    }

    // IMPLEMENTS INTERFACE CONCEPTLATTICE (util)
    /**
     * Access number of concept
     * 
     * @return nbr_concept
     */
    public int size() {
        return nbr_concept;
    }
}
