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

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import lattice.util.concept.Concept;

/**
 * @author Mr ROUME To change this generated comment edit the template variable
 *         "typecomment": Window>Preferences>Java>Templates. To enable and
 *         disable the creation of type comments go to
 *         Window>Preferences>Java>Code Generation.
 */

/*
 * Description : Ajout de quelques méthodes Copyright : Copyright (c) 2004
 * SociÈtÈ :Universite de Montréal @author Mame Awa Diop et Petko Valtchev
 * 
 * @version 1.1
 */

public class LatticeGraph extends AbstractCompleteConceptLattice {

    protected List<Node<Concept>> setOfNodes;

    protected Node<Concept> top = null;

    protected Node<Concept> bottom = null;

    protected double minSupp = 0;

    /**
     * Constructor for LatticeGraph.
     */
    public LatticeGraph() {
        super();
        setOfNodes = new Vector<Node<Concept>>();
    }

    /**
     * @see AbstractCompleteConceptLattice#size()
     */
    public int size() {
        return setOfNodes.size();
    }

    /**
     * @see AbstractCompleteConceptLattice#isEmpty()
     */
    public boolean isEmpty() {
        return (size() == 2 && top.getContent().getIntent().size() == 0 && bottom
                .getContent().getExtent().size() == 0);
    }

    /**
     * @see AbstractCompleteConceptLattice#getBottom()
     */
    public Node<Concept> getBottom() {
        return bottom;
    }

    public void setBottom(Node<Concept> N) {
        if (bottom != null && bottom.getChildren().size() == 0
            && bottom.getParents().size() == 0)
            setOfNodes.remove(bottom);
        bottom = N;
        if (N != null && !setOfNodes.contains(N))
            setOfNodes.add(N);
    }

    public void findNSetBottom() {
        int nbBot = 0;
        Node<Concept> theBot = null;
        for (int i = 0; i < setOfNodes.size() && nbBot < 2; i++) {
            if (setOfNodes.get(i).getChildren().size() == 0) {
                nbBot++;
                theBot = setOfNodes.get(i);
            }
        }
        if (nbBot == 1)
            bottom = theBot;
        else
            bottom = null;
    }

    /**
     * @see AbstractCompleteConceptLattice#getTop()
     */
    public Node<Concept> getTop() {
        return top;
    }

    public void setTop(Node<Concept> N) {
        if (top != null && top.getChildren().size() == 0
            && top.getParents().size() == 0)
            setOfNodes.remove(top);
        top = N;
        if (N != null && !setOfNodes.contains(N))
            setOfNodes.add(N);
    }

    public void findNSetTop() {
        int nbTop = 0;
        Node<Concept> theTop = null;
        for (int i = 0; i < setOfNodes.size() && nbTop < 2; i++) {
            if (setOfNodes.get(i).getParents().size() == 0) {
                nbTop++;
                theTop = setOfNodes.get(i);
            }
        }
        if (nbTop == 1)
            top = theTop;
        else
            top = null;
    }

    /**
     * @see AbstractCompleteConceptLattice#getTop()
     */
    public Collection<Node<Concept>> getAllNodes() {
        return setOfNodes;
    }

    public void add(Node<Concept> N) {
        setOfNodes.add(N);
    }

    // *****************************************************************************************************
    // *****************************************************************************************************
    // *****************************************************************************************************

    // ----> UNUSED METHODS COMMING FROM INTERFACE
    // AbstractCompleteConceptLattice <----

    // *****************************************************************************************************
    // *****************************************************************************************************
    // *****************************************************************************************************

    /**
     * @see AbstractCompleteConceptLattice#findBottom()
     */
    public Node<Concept> findBottom() {
        return null;
    }

    /**
     * @see AbstractCompleteConceptLattice#findTop()
     */
    public Node<Concept> findTop() {
        return null;
    }

    /**
     * @see AbstractCompleteConceptLattice#iterator()
     */
    public Iterator<Node<Concept>> iterator() {
        return null;
    }

    /**
     * @see AbstractCompleteConceptLattice#setNbOfNodes(int)
     */
    public void setNbOfNodes(int n) {
    }

    /**
     * @see AbstractCompleteConceptLattice#incNbOfNodes()
     */
    public void incNbOfNodes() {
    }

    /**
     * @see AbstractCompleteConceptLattice#set_max_transaction_size(int)
     */
    public void set_max_transaction_size(int m) {
    }

    /**
     * @see AbstractCompleteConceptLattice#getIntentLevelIndex()
     */
    public List<List<Node<Concept>>> getIntentLevelIndex() {
        return null;
    }

    /**
     * @see AbstractCompleteConceptLattice#initialiseIntentLevelIndex(int)
     */
    public void initialiseIntentLevelIndex(int size) {
    }

    /**
     * @see AbstractCompleteConceptLattice#addBottomToIntentLevelIndex(Node)
     */
    public void addBottomToIntentLevelIndex(Node<Concept> node) {
    }

    /**
     * @see AbstractCompleteConceptLattice#setUpperCover(Node, Node)
     */
    public void setUpperCover(Node<Concept> n1, Node<Concept> n2) {
    }

    public void remove(Node<Concept> node) {
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.util.structure.CompleteConceptLattice#setMinSupp(double)
     */
    public void setMinSupp(double d) {
        // TODO Auto-generated method stub

    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.util.structure.CompleteConceptLattice#getMinSupp()
     */
    public double getMinSupp() {
        return minSupp;
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.util.structure.CompleteConceptLattice#findNode(java.lang.Integer)
     */
    public Node<Concept> findNode(Integer conceptNodeID) {
        // TODO Auto-generated method stub
        return null;
    }

    public Node<Concept> getNode(Concept c) {
        // TODO Auto-generated method stub
        return null;
    }

}
