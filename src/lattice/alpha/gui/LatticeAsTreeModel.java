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
import javax.swing.tree.TreeNode;
import javax.swing.tree.TreePath;

/**
 * @author marc
 */
public class LatticeAsTreeModel implements TreeModel {
    private List<TreeModelListener> treeModelListeners;

    private TreeNode topNode;

    public LatticeAsTreeModel(TreeNode root) {
        treeModelListeners = new Vector<TreeModelListener>();
        topNode = root;
    }

    // //////////////Fire events //////////////////////////////////////////////

    /**
     * The only event raised by this model is TreeStructureChanged with the root
     * as path, i.e. the whole tree has changed.
     */
    protected void fireTreeStructureChanged(LatticeTreeNode oldRoot) {
        TreeModelEvent e = new TreeModelEvent(this, new Object[] { oldRoot });
        for (TreeModelListener listener : treeModelListeners) {
            listener.treeStructureChanged(e);
        }
    }

    // //////////////TreeModel interface implementation ///////////////////////

    /**
     * Adds a listener for the TreeModelEvent posted after the tree changes.
     */
    public void addTreeModelListener(TreeModelListener l) {
        treeModelListeners.add(l);
    }

    /**
     * Returns the child of parent at index index in the parent's child array.
     */
    public TreeNode getChild(Object parent, int index) {
        return ((TreeNode) parent).getChildAt(index);
    }

    /**
     * Returns the number of children of parent.
     */
    public int getChildCount(Object parent) {
        return ((TreeNode) parent).getChildCount();
    }

    /**
     * Returns the index of child in parent or -1 if the specified child is not
     * a child of the specified parent.
     * 
     * @param parent
     *            the parent
     * @param child
     *            the child
     * @return the index of child in parent or -1
     * @see javax.swing.tree.TreeModel#getIndexOfChild(java.lang.Object,
     *      java.lang.Object)
     */
    public int getIndexOfChild(Object parent, Object child) {
        TreeNode parentNode = (TreeNode) parent;
        return parentNode.getIndex((TreeNode) child);
    }

    /**
     * Returns the root of the tree.
     */
    public TreeNode getRoot() {
        return topNode;
    }

    /**
     * Returns true if the specified node is a leaf.
     */
    public boolean isLeaf(Object node) {
        return ((TreeNode) node).isLeaf();
    }

    /**
     * Removes a listener previously added with addTreeModelListener().
     */
    public void removeTreeModelListener(TreeModelListener l) {
        treeModelListeners.remove(l);
    }

    /**
     * Messaged when the user has altered the value for the item identified by
     * path to newValue. Not used by this model.
     */
    public void valueForPathChanged(TreePath path, Object newValue) {
        System.out.println("*** valueForPathChanged : " + path + " --> "
                           + newValue);
    }

}
