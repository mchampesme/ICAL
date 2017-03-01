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

import java.util.Vector;

import lattice.util.concept.Extent;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;

public class FCIRow extends FIRow
{
   private Vector gen;
   private int pred_supp;
   private boolean is_key;
   
   private Extent extent;

   public FCIRow(){
      super();
      gen = new Vector();
      pred_supp = Integer.MAX_VALUE;   // it imitates positive infinity
      extent = new SetExtent();
   }

   public FCIRow(Vector set) {
      super();
      gen = set;
      extent = new SetExtent();
   }

   public String toString() {
      return ""+gen+"; "+pred_supp+"; "+support+"; "+is_key+"; "+closure;
   }

   public Vector getGen() { return this.gen; }
   public Vector getGenerator() { return this.getGen(); }

   public void setGen(Vector gen) { this.gen = gen; }

   public int getPredSupp() { return this.pred_supp; }

   public void setPredSupp(int pred_supp) { this.pred_supp = pred_supp; }

   public boolean getIsKey() { return this.is_key; }

   public void setIsKey(boolean is_key) { this.is_key = is_key; }

   public void setSupport(int support) {
      this.support = support;
   }

   public void setClosure(Intent closure, Level p) {
      this.closure = closure;
//      p.addTrieClosure(closure, this);
   }
   
   public void setExtent(Extent ext) {
    this.extent = ext;
 }
   
   public Extent getExtent() { return this.extent; }
}
