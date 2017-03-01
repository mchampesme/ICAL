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
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import lattice.util.concept.Concept;
import lattice.util.structure.Node;

/**
 * <p>
 * A list of ConceptNode ordered according to the cardinality of their Intent.
 * </p>
 * 
 * @author Marc Champesme
 * @version 1.0
 */
public class NodeListByIntent {

    /**
     * Index of concepts by size (cardinality) of their intention
     */
    private List<Node<Concept>>[] intentLevelIndex;

    private int minIntentSize;

    private int maxIntentSize;

    private int nodeNumber;

    private boolean intentSizeIsInRange(int intentSize) {
        return intentSize >= minIntentSize && intentSize <= maxIntentSize;
    }

    @SuppressWarnings("unchecked")
	public NodeListByIntent(int attributeNumber) {
        intentLevelIndex =  (List<Node<Concept>>[]) new List[attributeNumber + 1];
        maxIntentSize = attributeNumber;
    }

    @SuppressWarnings("unchecked")
	public NodeListByIntent(int minIntentSize, int maxIntentSize) {
        intentLevelIndex = (List<Node<Concept>>[]) new List[maxIntentSize - minIntentSize + 1];
    }

    public int minIntentSize() {
        return minIntentSize;
    }

    public int maxIntentSize() {
        return maxIntentSize;
    }

    /**
     * @return Le premier �l�ment du vecteur i
     */
    public List<Node<Concept>> minIntentSizeConcepts() {
        if (intentLevelIndex[0] == null) {
            return Collections.emptyList();
        }
        return Collections.unmodifiableList(intentLevelIndex[0]);
    }

    /**
     * Returns the list of Node<Concept> with maximum intent cardinality, which
     * are present in this list.
     * 
     * @return the list of Node<Concept> with maximum intent cardinality
     */
    public List<Node<Concept>> maxIntentSizeConcepts() {
        if (intentLevelIndex[maxIntentSize - minIntentSize] == null) {
            return Collections.emptyList();
        }
        return Collections.unmodifiableList(intentLevelIndex[maxIntentSize
                                                             - minIntentSize]);
    }

    /**
     * Returns an unmodifiable view of the list of Node<Concept> with the
     * specified intent cardinality which are present in this list.
     * 
     * @param intentSize
     * @return an unmodifiable view of the list of Node<Concept> with the
     *         specified intent cardinality.
     */
    public List<Node<Concept>> get(int intentSize) {
        if (!intentSizeIsInRange(intentSize)
            || intentLevelIndex[intentSize - minIntentSize] == null) {
            return Collections.emptyList();
        }
        return Collections.unmodifiableList(intentLevelIndex[intentSize
                                                             - minIntentSize]);
    }

    public int size(int intentSize) {
        if (!intentSizeIsInRange(intentSize)
            || intentLevelIndex[intentSize - minIntentSize] == null) {
            return 0;
        }
        return intentLevelIndex[intentSize - minIntentSize].size();
    }

    /**
     * @return size
     */
    public int size() {
        return nodeNumber;
    }

    /**
     * Returns true if this list contains no elments with the specified intent
     * size.
     * 
     * @param intentSize
     * @return true if this list does not contains Node<Concept> with the
     *         specified intent cardinality ; false otherwise
     */
    public boolean isEmpty(int intentSize) {
        if (!intentSizeIsInRange(intentSize)
            || intentLevelIndex[intentSize - minIntentSize] == null) {
            return true;
        }
        return intentLevelIndex[intentSize - minIntentSize].isEmpty();
    }

    public Iterator<Node<Concept>> iterator() {
        return new NodeListByIntentIterator(this);
    }

    public Iterator<Node<Concept>> decIterator() {
        return new NodeListByIntentDecIterator(this);
    }

    public Iterator<Node<Concept>> iterator(int intentSize) {
        if (!intentSizeIsInRange(intentSize)
            || intentLevelIndex[intentSize - minIntentSize] == null) {
            List<Node<Concept>> theEmptyList = Collections.emptyList();
            return theEmptyList.iterator();
        }
        return intentLevelIndex[intentSize - minIntentSize].iterator();
    }

    /**
     * @param node
     */
    public void add(Node<Concept> node) {
        int intentSize = node.getContent().getIntent().size();
        if (intentLevelIndex[intentSize - minIntentSize] == null) {
            intentLevelIndex[intentSize - minIntentSize] = new ArrayList<Node<Concept>>();
        }
        intentLevelIndex[intentSize - minIntentSize].add(node);
    }

    public boolean contains(Node<Concept> node) {
        int intentSize = node.getContent().getIntent().size();
        if (intentLevelIndex[intentSize - minIntentSize] == null) {
            return false;
        }
        return intentLevelIndex[intentSize - minIntentSize].contains(node);
    }

    /**
     * @param node
     */
    public void remove(Node<Concept> node) {
        int intentSize = node.getContent().getIntent().size();
        if (intentLevelIndex[intentSize - minIntentSize] != null) {
            intentLevelIndex[intentSize - minIntentSize].remove(node);
        }
    }
}
