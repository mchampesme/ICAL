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

import java.util.List;
import java.util.Vector;

import javax.swing.event.TreeModelEvent;
import javax.swing.event.TreeModelListener;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreePath;

public class LatticeTreeModel implements TreeModel {
    private boolean showAncestors;
    private List<TreeModelListener> treeModelListeners = new Vector<TreeModelListener>();
    private LatticeTreeNode topNode;

    public LatticeTreeModel(LatticeTreeNode root) {
        showAncestors = false;
        topNode = root;
    }

    /**
     * Used to toggle between show ancestors/show descendant and
     * to change the root of the tree.
     */
    public void showAncestor(boolean b, Object newRoot) {
        showAncestors = b;
        LatticeTreeNode oldRoot = topNode;
        if (newRoot != null) {
           topNode = (LatticeTreeNode) newRoot;
        }
        fireTreeStructureChanged(oldRoot);
    }


//////////////// Fire events //////////////////////////////////////////////

    /**
     * The only event raised by this model is TreeStructureChanged with the
     * root as path, i.e. the whole tree has changed.
     */
    protected void fireTreeStructureChanged(LatticeTreeNode oldRoot) {
        TreeModelEvent e = new TreeModelEvent(this, 
                                              new Object[] {oldRoot});
        for (TreeModelListener listener : treeModelListeners) {
            listener.treeStructureChanged(e);
        }
    }


//////////////// TreeModel interface implementation ///////////////////////

    /**
     * Adds a listener for the TreeModelEvent posted after the tree changes.
     */
    public void addTreeModelListener(TreeModelListener l) {
        treeModelListeners.add(l);
    }

    /**
     * Returns the child of parent at index index in the parent's child array.
     */
    public LatticeTreeNode getChild(Object parent, int index) {
        LatticeTreeNode p = (LatticeTreeNode) parent;
        if (showAncestors) {
            return p.getParent(index);
        }
        return p.getChild(index);
    }

    /**
     * Returns the number of children of parent.
     */
    public int getChildCount(Object parent) {
        LatticeTreeNode p = (LatticeTreeNode) parent;
        if (showAncestors) {
            return p.getParentCount();
        }
        return p.getChildCount();
    }

    /**
     * Returns the index of child in parent.
     */
    public int getIndexOfChild(Object parent, Object child) {
        LatticeTreeNode parentNode = (LatticeTreeNode) parent;
         if (showAncestors) {
            return parentNode.getIndexOfParent(child);
        } else {
            return parentNode.getIndexOfChild(child);
        }
    }

    /**
     * Returns the root of the tree.
     */
    public LatticeTreeNode getRoot() {
        return topNode;
    }

    /**
     * Returns true if node is a leaf.
     */
    public boolean isLeaf(Object node) {
        LatticeTreeNode cNode = (LatticeTreeNode) node;
        if (showAncestors) {
            return cNode.isRoot();
        }
        return cNode.isLeaf();
    }

    /**
     * Removes a listener previously added with addTreeModelListener().
     */
    public void removeTreeModelListener(TreeModelListener l) {
        treeModelListeners.remove(l);
    }

    /**
     * Messaged when the user has altered the value for the item
     * identified by path to newValue.  Not used by this model.
     */
    public void valueForPathChanged(TreePath path, Object newValue) {
        System.out.println("*** valueForPathChanged : "
                           + path + " --> " + newValue);
    }
}
