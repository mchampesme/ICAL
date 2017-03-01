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

package lattice.util.index;

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import lattice.util.concept.Concept;
import lattice.util.structure.ConceptLatticeIterator;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
import lattice.util.structure.Node;

/**
 * <p>
 * Title: LevelIndex
 * </p>
 * <p>
 * Description: Structure d'indexation des concepts d'un
 * AbstractCompleteConceptLattice suivant la relation d'ordre
 * </p>
 * <p>
 * Copyright: Copyright (c) 2002
 * </p>
 * <p>
 * Company: Université de Montréal
 * </p>
 * 
 * @author David Grosser
 * @version 1.0
 */
public class LevelIndex implements Iterable<Node<Concept>> {

    private List<List<Node<Concept>>> intent_level_index; // Index des concepts
                                                        // par la taille

    // (cardinalité) de leur intention

    public LevelIndex() {
        intent_level_index = new Vector<List<Node<Concept>>>();
    }

    /**
     * Mettre a jour le vecteur intent_level_index.
     * 
     * @return intent_level_index
     */
    public List<List<Node<Concept>>> get_intent_level_index() {
        return intent_level_index;
    }

    /**
     * @return the last element
     */
    public List<Node<Concept>> lastElement() {
        return intent_level_index.get(intent_level_index.size() - 1);
    }

    /**
     * @param i
     * @return
     */
    public List<Node<Concept>> get(int i) {
        return intent_level_index.get(i);
    }

    /**
     * @return size
     */
    public int size() {
        return intent_level_index.size();
    }

    /**
     * Ajout d'un nouveau Vecteur a l'index
     * 
     * @param v
     */
    public void add(List<Node<Concept>> v) {
        intent_level_index.add(v);
    }

    /**
     * @param i
     * @return Le premier élément du vecteur i
     */
    public Node<Concept> first(int i) {
        return get(i).get(0);
    }

    /**
     * @param i
     * @return ture or false
     */
    public boolean isEmpty(int intentLevel) {
        return intent_level_index.get(intentLevel).isEmpty();
    }

    /**
     * @param size
     */
    public void initialiseIntentLevelIndex(int size) {
        for (int i = 0; i < size; i++) {
            intent_level_index.add(new Vector<Node<Concept>>());
        }
    }

    /**
     * @param node
     */
    public void addNodeToIntentLevelIndex(Node<Concept> node) {
        int nodeIntentSize = node.getContent().getIntent().size();
        if (nodeIntentSize >= intent_level_index.size())
            for (int i = intent_level_index.size(); i <= nodeIntentSize; i++) {
                List<Node<Concept>> newVect = new Vector<Node<Concept>>();
                intent_level_index.add(newVect);
            }
        intent_level_index.get(nodeIntentSize).add(node);

    }

    /**
     * @param node
     */
    public void addBottomToIntentLevelIndex(Node<Concept> node) {
        lastElement().add(node);
    }

    /**
     * @param node
     */
    public void removeNodeFromIntentLevelIndex(Node<Concept> node) {
        lastElement().remove(node);
    }

    /**
     * @param node
     */
    public void removeBottomFromIntentLevelIndex(Node<Concept> node) {
        lastElement().remove(node);
    }

    public Iterator<Node<Concept>> iterator() {
        return new ConceptLatticeIterator(intent_level_index);
    }

}
