/*
 ***********************************************************************
 * Copyright (C) 2004 The Galicia Team 
 *
 * Modifications to the initial code base are copyright of their
 * respective authors, or their employers as appropriate.  Authorship
 * of the modifications may be determined from the ChangeLog placed at
 * the end of this file.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
 * USA; or visit the following url:
 * http://www.gnu.org/copyleft/lesser.html
 *
 ***********************************************************************
 */


/*****************************************************************
 * Source code information
 * -----------------------
 * 
 * Last modified on   $Date: 2004/10/26 19:20:38 $
 *               by   $Authors: Diop, Amine, Kamal$
 * Created on 2004-08-31
 *****************************************************************/

package lattice.util.trie;
import java.util.HashMap;

public class TrieNode {

	private Object flag; // the encoding data within a node such as formal attribute in the intent trie
	private Object data; // the data stored by the trie such as lattice concepts
	private HashMap children ;
	private int depth ;
	private TrieNode parent;
	boolean terminal; // when the trie node is a terminal, the variable gets the true value

	public TrieNode (){
		
		data=null;
		children = new HashMap();
		parent=null;
		depth = 0;
		terminal=false;
	}

	public TrieNode (Object flag){
		this.flag = flag;
		data=null;
		children = new HashMap();
		parent=null;
		depth = 0;
		terminal=false;
	}

	
	//returns the flag content of the trie node 
	public Object getFlag (){
		return flag ;
	}
	
	//idem
	public String toString (){
		return flag.toString() ;
	}
	
	public HashMap getChildren (){
		return children ;
	}
	
	public Object getData (){
		return data ;
	}
	
	
	public void setData (Object data){
		this.data=data;
	}
	
	public int getDepth (){
		return depth ;
	}
	
	public void setDepth ( int depth){
		this.depth = depth ;
	}
	
	public void addChildNode (Object flag) {
		if(isChild(flag)==null){
			TrieNode newChild = new TrieNode(flag);
			newChild.setParent(this);
			this.getChildren().put(flag,newChild);
		}
	}
	
	public void setParent (TrieNode parent) {
		this.parent = parent;
	}
	
	public void removeChild (TrieNode node) {
		children.remove(node.getFlag());
	}
	
	// checks whenever the given flag is a valid 
	// child within the current trie node
	public TrieNode isChild (Object flag) {
		return (TrieNode)this.getChildren().get(flag);
	}
	
	public TrieNode getParent ( ) {
		return parent ;
	}

	public void setFlag (Object newFlag) {
		flag = newFlag ;
	}
	
	public boolean isLeaf() {
		return (children.isEmpty());
		}
	
	public void setTerminal(boolean  terminal){
		this.terminal = terminal;
		}
	
	public boolean isTerminal() {
		return terminal;
		}
}
