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
package lattice.alpha.gui;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import javax.swing.tree.TreeNode;

import lattice.util.concept.Concept;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.Node;

/**
 * @author marc
 */
public class LatticeAsTreeConceptNode implements TreeNode {
    private Node<Concept> myNode;

    private LatticeAsTreeConceptNode myFather;

    private List<Node<Concept>> conceptNodeChildren;

    private List<FormalObject> formalObjectChildren;

    private int childCount;

    private TreeNode[] treeNodeChildren;

    private List<Intent> generators;

    public LatticeAsTreeConceptNode(Node<Concept> name) {
        myNode = name;
        conceptNodeChildren = name.getChildren();
        if (conceptNodeChildren.size() == 1
                && conceptNodeChildren.get(0).getChildren()
                        .isEmpty()) {
            conceptNodeChildren = Collections.emptyList();
            }
        formalObjectChildren = leafChildren(myNode);
        childCount = conceptNodeChildren.size() + formalObjectChildren.size();
        treeNodeChildren = new TreeNode[childCount];
        generators = myNode.getContent().getGenerator();
    }

    public LatticeAsTreeConceptNode(LatticeAsTreeConceptNode father,
                                    ConceptNode aNode) {
        this(aNode);
        myFather = father;
        generators = reduceGenerators(myFather.myNode.getContent().getIntent(),
                                      generators);
    }

    /*
     * (non-Javadoc)
     * 
     * @see javax.swing.tree.TreeNode#children()
     */
    public Enumeration<TreeNode> children() {
        return new TreeNodeChildrenEnumeration(this);
    }

    /*
     * (non-Javadoc)
     * 
     * @see javax.swing.tree.TreeNode#getAllowsChildren()
     */
    public boolean getAllowsChildren() {
        return getChildCount() != 0;
    }

    /*
     * (non-Javadoc)
     * 
     * @see javax.swing.tree.TreeNode#getChildAt(int)
     */
    public TreeNode getChildAt(int childIndex) {
        TreeNode tnChild = treeNodeChildren[childIndex];
        if (tnChild == null) {
            if (childIndex < conceptNodeChildren.size()) {
                ConceptNode cnChild = (ConceptNode) conceptNodeChildren
                        .get(childIndex);
                tnChild = new LatticeAsTreeConceptNode(this, cnChild);
            } else {
                FormalObject foChild = (FormalObject) formalObjectChildren
                        .get(childIndex - conceptNodeChildren.size());
                if (foChild != null) {
                    tnChild = new LatticeAsTreeFObjectNode(this, foChild);
                }
            }
            treeNodeChildren[childIndex] = tnChild;
        }
        return tnChild;
    }

    /*
     * (non-Javadoc)
     * 
     * @see javax.swing.tree.TreeNode#getChildCount()
     */
    public int getChildCount() {
        return childCount;
    }

    /*
     * (non-Javadoc)
     * 
     * @see javax.swing.tree.TreeNode#getIndex(javax.swing.tree.TreeNode)
     */
    public int getIndex(TreeNode child) {
        int index = -1;
        for (int i = 0; i < childCount && index == -1; i++) {
            if (child.equals(treeNodeChildren[i])) {
                index = i;
            }
        }
        return index;
    }

    /*
     * (non-Javadoc)
     * 
     * @see javax.swing.tree.TreeNode#getParent()
     */
    public TreeNode getParent() {
        return myFather;
    }

    /*
     * (non-Javadoc)
     * 
     * @see javax.swing.tree.TreeNode#isLeaf()
     */
    public boolean isLeaf() {
        return childCount == 0;
    }

    public String toString() {
        Concept myConcept = myNode.getContent();
        return generators.toString() + " (" + myConcept.getExtent().size()
               + ")";
    }

    private static List<Intent> reduceGenerators(Intent fatherIntent, List<Intent> stdGenerators) {
        List<Intent> reducedGenerators = new LinkedList<Intent>();
        for (Intent currentGenerator : stdGenerators) {
            Intent reducedGenerator = currentGenerator.clone();
            reducedGenerator.removeAll(fatherIntent);
            if (!reducedGenerator.isEmpty()
                && !reducedGenerators.contains(reducedGenerator)) {
                reducedGenerators.add(reducedGenerator);
            }
        }
        return reducedGenerators;
    }

    private static List<FormalObject> leafChildren(Node<Concept> myNode2) {
        Set<FormalObject> remainingFObjects = new HashSet<FormalObject>(myNode2.getContent()
                .getExtent());
        for (Node<Concept> childNode : myNode2.getChildren()) {
            remainingFObjects.removeAll(childNode.getContent().getExtent());
        }
        return new ArrayList<FormalObject>(remainingFObjects);
    }

}
