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
 * Created on 2004-10-11
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package lattice.util.titanic;

/**
 * @author nehmekam
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

import java.util.*;

import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import lattice.util.trie.*;

public class Key
{
	   private Vector keys;
	   private AbstractTrie trie;

	   public Key() {
	      this.keys = new Vector();
	      this.trie = new AbstractTrie();
	   }

	   public void add(FIRow row) {
	      this.keys.add(row);
	      this.trie.add(((FCIRow)row).getGen(), row);
//	      this.trie.add(((Row_p)row).getClosure(), row);
	   }

	   public Vector getKeys() {
	      return this.keys;
	   }

	   public AbstractTrie getTrie() {
	      return this.trie;
	   }

	   public String toString() {
	      Vector v = new Vector();
	      FCIRow row;

	      for (Enumeration e = this.keys.elements(); e.hasMoreElements(); )
	      {
	         row = (FCIRow)e.nextElement();
	         v.add(row.getGen());
	      }
	      return v.toString();
	   }

	   public Key pruneKeyPrime()
	   {
	      Key key_prime = new Key();
	      FCIRow row;

	      for (Enumeration e = this.getKeys().elements(); e.hasMoreElements(); )
	      {
	         row = (FCIRow)e.nextElement();
	         if (row.getSupport() != -1) key_prime.add(row);
	      }
	      return key_prime;
	   }

	   public FormalAttribute[][] getGenerators()
	   {
	      int i, k, m;
	      FCIRow row;
	      Vector bs;
	      int size       = this.keys.size();
	      FormalAttribute[][] result = new FormalAttribute[size][];

	      for (k = 0; k<size; ++k)
	      {
	         row = (FCIRow)this.keys.get(k);
	         bs = row.getGen();
	         result[k] = new FormalAttribute[bs.size()];
	         m = 0;
	         Iterator iter = (Iterator)bs.iterator();
	         while(iter.hasNext()){
	         	FormalAttribute fa = (FormalAttribute)iter.next();
	         	result[k][m++] = fa;
	         }
	         //sort(result[k],bs.size());
	      }
	      
	      return result;
	   }
	   
	   public void sort(FormalAttribute[] v,int l){
	   	TreeSet v1 = new TreeSet();
	   	for (int i=0; i<v.length;i++){
	   		FormalAttribute fatt = (FormalAttribute)v[i];
	   		if (fatt.getName().startsWith("att_")){
	   			Integer value = new Integer(fatt.getName().substring(4,fatt.getName().length()));
	   			v1.add(value);
	   		}
	   	}
	   	v = new FormalAttribute[l];
	   	Iterator itr = v1.iterator();
	   	int j = 0;
	   	while (itr.hasNext()){
	   		Integer val = (Integer)itr.next();
	   		String str = new String("att_"+val.toString());
	   		FormalAttribute fat = new DefaultFormalAttribute(str);
	   		v[j++] = fat;
	   	}
	   }
	   
	}

