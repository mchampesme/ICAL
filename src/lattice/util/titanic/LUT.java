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
 * Created on 2004-10-18
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package lattice.util.titanic;

import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.FormalAttribute;

/**
 * @author nehmekam
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
class LUT
{
   private FormalAttribute lut[];                    // lookup table

   LUT() {
      this(300);                             // default size if no parameter was given
   }

   LUT(final int size) {
      lut = new FormalAttribute[size+1];             // for ex. max. element is 3, then we need to make this: [0][1][2][3]
      for (int i = 0; i<lut.length; ++i)
         lut[i] = new DefaultFormalAttribute(new Integer(i).toString());
   }

   public FormalAttribute getInteger(int i) {
      if (i >= lut.length) resize(i);
      return lut[i];
   }

   private void resize(int new_size) 
   {
   	FormalAttribute[] new_lut = new FormalAttribute[new_size+1];
      System.arraycopy(lut,0, new_lut,0, lut.length);
      for (int i = lut.length; i<new_lut.length; ++i)
         new_lut[i] = new DefaultFormalAttribute(new Integer(i).toString());

      this.lut = new_lut;
   }

   public void trimToSize(int new_size)
   {
   	FormalAttribute[] new_lut = new FormalAttribute[new_size+1];
      System.arraycopy(lut,0, new_lut,0, new_lut.length);
      this.lut = new_lut;
   }

   public String toString()
   {
      StringBuffer sb = new StringBuffer();
      sb.append("{");
      for (int i = 0; i < lut.length; ++i)
         sb.append((i>0?", ":"")+i);
      sb.append("}");

      return sb.toString();
   }
}