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
import java.util.LinkedList;
import java.util.TreeSet;
import java.util.Vector;

import lattice.util.concept.Concept;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;




/**
 * @author diopmame
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class KLS_Trie extends AbstractTrie {

	
	//Constructeur
	public KLS_Trie() {
		super();
	}

	
	// Retourne la cle la plus longue
	/*public Concept getLongestKey(){
		
		Concept toreturn = getLongestKey(super.root) ;
		remove(toreturn);
		return 	toreturn;
	}*/
	
	//idem
	/*private  Concept getLongestKey(TrieNode roOT){
	
	 	conceptARetourner = new ConceptImp(new SetExtent(), new SetIntent());
		TrieNode trieNode ;
		int i ;
		int longKey = 1 , longIndex = 0  ;
		
		Object data = null;
	
		

		for( i = 0 ; i < leafs.size() ; i++) {
			
			trieNode = (TrieNode)leafs.get(i);
			data = trieNode.getData();
			while(trieNode.getParent() != null){
				intent.add(trieNode.getFlag());
				trieNode = trieNode.getParent() ;
			}
			
			conceptARetourner.setIntent((Intent)intent);
			
			if (((TrieNode)leafs.get(i)).getDepth() >= longKey ){
				concept = conceptARetourner ;
				longKey = ((TrieNode)leafs.get(i)).getDepth() ;
				longIndex = i ;
			}
			
			conceptARetourner = new ConceptImp(new SetExtent(), new SetIntent());
			intent = new SetIntent() ;		
		
		
		}
		leafs.remove(longIndex);
		
		
		return concept ;
	}
	*/
	
	/*private  Object getLongestKey(TrieNode node){
		
	
			TrieNode trieNode = null ;
			TrieNode parentNode = null;
			
			int i ;
			int longKey = 1 , longIndex = 0  ;
			
			Object data = null;
			
			TreeSet encoding = new TreeSet() ;
			
			//System.out.println("leafs.size(): "+leafs.size());
		

			for( i = 0 ; i < leafs.size() ; i++) {
				
				trieNode = (TrieNode)leafs.get(i);
				
				parentNode = trieNode;
				
				data = trieNode.getData();
				
				//System.out.println("data: "+data+" ... depth: "+trieNode.getDepth());
				
				
				while(parentNode != null){
					trieNode = parentNode;
					if (trieNode.getFlag() != null)
						encoding.add(trieNode.getFlag());
					parentNode = trieNode.getParent();	
				}
				
				if (((TrieNode)leafs.get(i)).getDepth() >= longKey ){
					longKey = ((TrieNode)leafs.get(i)).getDepth() ;
					longIndex = i ;
				}
				
			}
			
			if (!leafs.isEmpty()){
				leafs.remove(longIndex);
				//System.out.println("new leafs.size(): "+leafs.size());
			}
			
			//System.out.println("encoding: "+encoding);
		
			//TrieNode exist = this.contains(encoding);
			//data = exist.getData();
			
			remove(encoding);
			
			return data;
			
		}*/
	
	private  Object getLongestKey(TrieNode node){
		
			TrieNode trieNode = null ;
			TrieNode longestKey = null;
			
			
			int longKey = 0 ;
			
			Object data = null;
			
			TreeSet encoding = new TreeSet() ;
			
			Vector v = new Vector();
			
			this.traverseLeafs(this.getRoot(),v);
			
			for (int i=0;i<v.size();i++){
				trieNode = (TrieNode)v.elementAt(i);
				
				if (trieNode.getDepth()>longKey){
					longKey = trieNode.getDepth();
					longestKey = trieNode;
				}
			}
			
			
			data = longestKey.getData();
			
			while (longestKey.getParent() != null){
				if (longestKey.getFlag() !=null)
					encoding.add(longestKey.getFlag());
				longestKey = longestKey.getParent();
			}
			remove(encoding);
			return data;
	}
	
	
	
	public Object getLongestKey(){
		
		//Object toreturn = getLongestKey(this.getRoot()) ;
		
		//remove((Collection)toreturn;
		
		
		return getLongestKey(this.getRoot());
	}


	
	/*public void put(Concept concept) {
		
	}

	public boolean remove(Concept concept) {
		return false;
	}

	public Concept get(Concept concept) {
		return null;
	}*/
	
	
	
}
