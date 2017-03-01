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

import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;
import java.util.Vector;
import java.util.Iterator;

import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import lattice.util.concept.SetIntent;
import lattice.util.trie.*;

/**
 * @author 
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class Level extends AbstractLevel
{
   private Map map;
   private Map genMap;        // generator map
   private AbstractTrie trie;
   private Key key,
               key_prime;

   public Level() {
      this.map  = new HashMap();
      this.genMap = new HashMap();
      this.trie = new AbstractTrie();
      this.key  = new Key();
      this.key_prime = new Key();
   }

   public void reinit() {
      super.reinit();
      this.map  = new HashMap();
      this.genMap = new HashMap();
      this.trie = new AbstractTrie();
      this.key  = new Key();
      this.key_prime = new Key();
   }

   public void addKey(FIRow row) {
      this.key.add(row);
   }

   public void fillKeyPrime() {
      this.key_prime = this.key.pruneKeyPrime();
   }

   public Key getKey() { return this.key; }
   public Key getKeys() { return this.getKey(); }

   public Key getKeyPrime() { return this.key_prime; }

   public Vector getSubsetsOf(Vector set) {
      return this.trie.getSubsetsOf(set);
   }

   public AbstractTrie getTrie() {
      return this.trie;
   }

   public void freeTrie() {   // free up the memory
      this.trie = null;
   }

   public void add_row(Vector set) {
   	FIRow row = new FCIRow(set);
      add_row(row);
   }

   public void add_row(FIRow row) {                        // this function guarantees, that there will be 
//      BitSet closure = row.getClosure();                 // no duplicates of closures in the table
//      if (this.map.containsKey(closure) == false)        // this closure is not yet in
//      {
         rows.add(row);                                           // put the row in the table
         this.trie.add(((FCIRow)row).getGen(), row);    // add the generator to the trie
         this.genMap.put(((FCIRow)row).getGen(), row);
//         this.map.put(closure, row);
//      }
   }

   public FIRow getRowByGen(Vector gen) {
      return (FIRow)this.genMap.get(gen);
   }

   public String toStringAsClose() 
   {
      StringBuffer sb = new StringBuffer();
      FIRow row;
      for (Enumeration e = rows.elements(); e.hasMoreElements(); )
      {
         row = (FIRow)e.nextElement();
         sb.append(row.getClosure()+" ("+row.getSupport()+")");
         sb.append("\n");
      }
      return sb.toString();
   }

   public String toString()
   {
      StringBuffer sb = new StringBuffer();
      sb.append("Key: "+this.key.toString()+"\n");
      sb.append("Key prime: "+this.key_prime.toString()+"\n");
      sb.append(super.toString());

      return sb.toString();
   }

   public Map getMap() {
      return this.map;
   }

   public FormalAttribute[][] getGenerators()
   {
      int i, k, m;
      FCIRow row;
      Vector bs;
      int size       = this.getRows().size();
      FormalAttribute[][] result = new FormalAttribute[size][];

      for (k = 0; k<size; ++k)
      {
         row = (FCIRow)this.getRows().get(k);
         bs = row.getGen();
         result[k] = new FormalAttribute[bs.size()];
         m = 0;
         
         Iterator iter = (Iterator) bs.iterator();
         while(iter.hasNext()){
         	FormalAttribute fa = (FormalAttribute)iter.next();
         	result[k][m++] = fa;
         	
         }   
      }

      return result;
   }

   public Vector createCandidate(FormalAttribute[] a, FormalAttribute b)
   {
      Vector set = new Vector();
      for (int i = 0; i < a.length; ++i)
         set.add(a[i]);
      set.add(b);
      return set;
   }

   public static Vector get_i_subsets(Vector generator)  // make all the subsets of the given generator
   {                                                     // subsets' size is 1 smaller than the size of the generator
      Vector v = new Vector();
      
      Iterator itr = (Iterator) generator.iterator();
      while(itr.hasNext()){
      	Vector gen = (Vector) generator.clone();
      	FormalAttribute fa = (FormalAttribute)itr.next();
      	gen.remove(fa);
      	v.add(gen.clone());
      }
      return v;
   }

   // remove non-key elements
   public void prune()
   {
      Vector rows_new = new Vector();

      FCIRow row;
      for (Enumeration e = this.rows.elements(); e.hasMoreElements(); )
      {
         row = (FCIRow)e.nextElement();
         if (row.getIsKey()) rows_new.add(row);
      }
      this.rows = rows_new;
   }
}

