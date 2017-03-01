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

/*
 * Created on 2004-08-31
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package lattice.util.trie;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;
import java.util.TreeSet;
import java.util.Vector;

import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;



/**
 * @author diopmame
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public  class AbstractTrie  {
	
	protected TrieNode root ;
	protected LinkedList leafs = new LinkedList() ;
	
	public AbstractTrie() {
		root = new TrieNode();
	}
	
	public TrieNode getRoot() {
		return root;
		}

	public boolean isEmpty () { 
		return (root.getChildren().isEmpty());
	}

	/*
	public void put (Concept concept){
		// Separer l'extent de l'intent
		SetIntent intent = (SetIntent) concept.getIntent() ;
		SetExtent extent = (SetExtent) concept.getExtent() ;
		
		
		int i = 0 , index = 0 ;
		TrieNode node = root , newNode = null ;
		boolean duplicate = false ;
		Iterator it = intent.iterator();
		Object k  ;
		while ( it.hasNext()){
			k =  it.next() ;
			index = node.isChild(k) ;
			if( index < 0 ){
				newNode = new TrieNode(k) ;
				newNode.setParent(node) ;
				node.addChildNode(newNode) ;
				node = newNode ;
				duplicate = false ;
			}
			else{
				node = (TrieNode) node.getChildren().get(index) ;
				duplicate = true ;
			}
			i++;
		}
		node.setData(extent) ;
		node.setDepth(i);
			
		if ( duplicate == false )
		leafs.add(node) ;
	}
*/
	
	// Enleve un concept
	/*public boolean remove (Concept concept){
		SetIntent intent = (SetIntent) concept.getIntent() ;
		SetExtent extent = (SetExtent) concept.getExtent() ;
			
			int i = 0 , index = 0 ;
			boolean toReturn = false ;
			TrieNode node = root , newNode , lastNode ;
			Iterator it = concept.getIntent().iterator();
			Object k;
			
			while (it.hasNext()) {
				k =  it.next() ;
				
				index = node.isChild(k);
				if (index == -1 )
					break ;
				else{
					node = (TrieNode) node.getChildren().get(index) ;
				}
			}
		if ( it.hasNext() == false ) {
			
			node.setData(new SetExtent()) ;
			toReturn = true ;
			do{
				if ( !node.getData().equals(new SetExtent()) ){
					leafs.add(node) ;
					break ;
				}
				if (node.getChildren().size() > 0 )
					break ;
				lastNode = node ;
				node = node.getParent() ;
				node.removeChild(lastNode) ;
			}while (node.getParent() != null );
			
			
		}

			return toReturn ;
	}
	*/
	
	
	
	//Recupere un concept dans le trie 
	/*public Concept get (Concept concept){
		return get(concept,root);
	}*/
	

	//idem
	/*private Concept get (Concept concept , TrieNode roOT ){
		int i = 0 , index = 0 ;
		
		TrieNode node = root , newNode ;
		Iterator it = concept.getIntent().iterator();
		Object k = "" , token = "";
		while (it.hasNext()) {
			k =  it.next() ;
			
			index = node.isChild(k);
			if (index == -1 )
				return (new ConceptImp (new SetExtent() , new SetIntent()  )) ;
			else{
				node = (TrieNode) node.getChildren().get(index) ;
			}
				
				
		}
		
		return concept ;
	}*/
	
	public void add(Collection encoding, Object data)
	{
	TrieNode current = root;
	Iterator iter = (Iterator)encoding.iterator();

	while(iter.hasNext()){
		Object flag = (Object)iter.next();
		current.addChildNode(flag);
		current= current.isChild(flag);
	}

	current.setTerminal(true);
	current.setData(data);
	current.setDepth(encoding.size());
	
	//if (!leafs.contains(current) && current != this.getRoot()){
	if (!leafs.contains(current)){
		leafs.add(current);
		//System.out.println("After adding a new elt, new leafs.size()= "+leafs.size());
	}
	}
	
	/*public void remove(Collection encoding)
	{
		if (!encoding.isEmpty()){
			TrieNode exist = this.contains(encoding);
	
			if (exist !=null){
				
				TrieNode parent = null;
		
				while (exist.getFlag() != null){
					parent = exist.getParent();
					parent.removeChild(exist);
			
					if(parent.isLeaf()){
						this.leafs.add(parent);
						break;
					}
					exist = parent;
				}
		
			}
		}
	}*/
	
	public void remove(Collection encoding)
	{
		if (!encoding.isEmpty()){
			TrieNode exist = this.contains(encoding);
	
			if (exist !=null){
				
				TrieNode parent = exist.getParent();
				parent.removeChild(exist);
				
		
				while ((parent.getChildren().isEmpty()) && (!parent.isTerminal()) && (parent != this.getRoot())){
					exist = parent;
					parent = exist.getParent();
					parent.removeChild(exist);
				}
					
					if((parent.isTerminal()) && (parent.getChildren().isEmpty())){
						this.leafs.add(parent);
					}								
			}
		}
	}
	
	public TrieNode contains(Collection encoding)
	{
		/*TrieNode current = root;
		
		Iterator itr = (Iterator)encoding.iterator();

		while((itr.hasNext())&& (current!=null)){
			Object flag = (Object)itr.next();
			current = (TrieNode)(current.isChild(flag));
		}

		return current;*/
		
		TrieNode curr = root;
		Iterator itr = (Iterator)encoding.iterator();

		while((itr.hasNext())&& (curr!=null)){
			Object i = (Object)itr.next();
			curr = (TrieNode)(curr.getChildren().get(i));
		}

		if ((curr!=null) && (curr.isTerminal())) return curr;
		// else
		return null;
	}
	
	public Vector getSubsetsOf(Vector set)
	{
	Vector result = new Vector();

	findSubsetsOf((Vector)set, getRoot(), result);

	return result;
	}
	
	public void traverseWords(TrieNode node)
	{
		Iterator i;
		TrieNode curr;
		if (node != null)
		{
			for (i = node.getChildren().values().iterator(); i.hasNext(); )
			{
				curr = (TrieNode)i.next();
				if (curr.isTerminal()) System.out.println(curr.getData());
				traverseWords(curr);
			}
		}
	}
	
	public void findSubsetsOf( Vector set, TrieNode curr, Vector v)
	{
		if (curr == null) return;
		// else
		Vector copy;
		TrieNode child;
		if (curr.isTerminal()) v.add(curr.getData());

		Iterator iter = (Iterator)set.iterator();
		while(iter.hasNext()){
			Object i = (Object)iter.next();
			child = (TrieNode)(curr.getChildren().get(i));
			if (child != null){      // if the child at position i exists
				copy = (Vector)set.clone();
				copy.remove(i);
				findSubsetsOf(copy, child, v);
			}
		}
	}
	
	public boolean contain(Collection word)
	{
		TrieNode curr = root;
		Iterator itr = (Iterator)word.iterator();

		while((itr.hasNext())&& (curr!=null)){
			Object i = (Object)itr.next();
			curr = (TrieNode)(curr.getChildren().get(i));
		}

		if ((curr!=null) && (curr.isTerminal())) return true;
		// else
		return false;
	}
	
	public void buvetteAdd(Collection encoding, Object data)
	{
		
	boolean duplicate = false ;
	TrieNode current = root;
	Iterator iter = (Iterator)encoding.iterator();

	while(iter.hasNext()){
		Object flag = (Object)iter.next();
		
		if((TrieNode)current.getChildren().get(flag) == null){
			TrieNode newChild = new TrieNode(flag);
			newChild.setParent(current);
			current.getChildren().put(flag,newChild);
			duplicate = false ;
			current = newChild;
		}
		
		else{
			current = current.isChild(flag);
			duplicate = true ;
		}
		
	}
	
	current.setTerminal(true);
	current.setData(data);
	current.setDepth(encoding.size());
	
	
	
	/*if (current != this.getRoot()){
		TrieNode parentNode = current.getParent();
		parentNode.getChildren().remove(current.getFlag());
		parentNode.getChildren().put(current.getFlag(),current);
	}*/

	
	if ( duplicate == false){
		leafs.add(current);
		//System.out.println("new Trie Node: "+current.getFlag()+" ... "+current.getData()+" ... "+current.getDepth());
	}
	//else
		//System.out.println(" Trie Node modified: "+current.getFlag()+" ... "+current.getData()+" ... "+current.getDepth());
	
	}
	
	public void traverseLeafs(TrieNode node,Vector v)
	{
		Iterator i;
		TrieNode curr;
		if (node != null)
		{
			for (i = node.getChildren().values().iterator(); i.hasNext(); )
			{
				curr = (TrieNode)i.next();
				if (curr.isLeaf()) v.add(curr);
				traverseLeafs(curr,v);
			}
		}
	}
	
}
	
	


