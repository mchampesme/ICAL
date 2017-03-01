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

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import lattice.util.concept.Concept;
import lattice.util.concept.Intent;
import lattice.util.structure.Node;

public class LatticeTreeNode {
    private Node<Concept> myNode;
    private Node<Concept> myFather;
    private List<Node<Concept>> parents;
    private List<Node<Concept>> children;
    private List<Intent> generators;
    
    public LatticeTreeNode(Node<Concept> aNode) {
        myNode = aNode;
        parents = Collections.list(Collections.enumeration(aNode.getParents()));
        children = aNode.getChildren();
        generators = myNode.getContent().getGenerator();
    }

    public LatticeTreeNode(Node<Concept> father, Node<Concept> aNode) {
        myNode = aNode;
        parents = Collections.list(Collections.enumeration(aNode.getParents()));
        children = aNode.getChildren();
        myFather = father;
    }

    public LatticeTreeNode getChild(int index) {
        return new LatticeTreeNode(this.myNode, children.get(index));
    }
    
    public int getChildCount() {
        return children.size();
    }
    
    public int getIndexOfChild(Object child) {
        return children.indexOf(((LatticeTreeNode) child).myNode);
    }
    
    public boolean isLeaf() {
        return children.isEmpty();
    }
    
    public LatticeTreeNode getParent(int index) {
        return new LatticeTreeNode(parents.get(index));
    }
    
    public int getParentCount() {
        return parents.size();
    }
    
    public int getIndexOfParent(Object parent) {
        return parents.indexOf(((LatticeTreeNode) parent).myNode);
    }
    
    public boolean isRoot() {
        return parents.isEmpty();
    }
    
    public void reduceGenerators() {
        Intent fatherIntent = myFather.getContent().getIntent();
        List<Intent> reducedGenerators = new LinkedList<Intent>();
        
        for (Intent currentGenerator : myNode.getContent().getGenerator()) {
            Intent reducedGenerator = currentGenerator.clone();
            reducedGenerator.removeAll(fatherIntent);
            if (!reducedGenerator.isEmpty() && !reducedGenerators.contains(reducedGenerator)) {
                reducedGenerators.add(reducedGenerator);
            }
        }
        generators = reducedGenerators;
    }
    
    public String toString() {
        Concept myConcept = myNode.getContent();
        if (myFather != null && generators == null) {
            reduceGenerators();
        }
        return generators.toString() + " (" + myConcept.getExtent().size() + ")";
    }
}
