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

package lattice.util.concept;

import java.util.Iterator;
import java.util.TreeSet;

/**
 * <p>Titre : Lattice</p>
 * <p>Description : Manipulation des treillis</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : Université de MontrŽal</p>
 * @author David Grosser
 * @version 1.0
 */
public class SetExtent extends TreeSet<FormalObject> implements Extent {

  public SetExtent() {
    super();
  }

  public Extent extentUnion(Extent extent) {
    Extent result;
    if(extent.size() > this.size()) {
      result = (Extent) extent.clone();
      result.addAll(this);
    }
    else {
      result = (Extent)this.clone();
      result.addAll(extent);
    }
    return result;
  }

  /**
   *
   * @param extent
   * @return result
   */
  public Extent extentIntersection(Extent extent)
  {
    Extent result =new SetExtent();
    if(!this.isEmpty() && !extent.isEmpty())
    {
      Iterator<FormalObject> it1 = this.iterator();
      Iterator<FormalObject> it2 = extent.iterator();
      FormalObject c1, c2;
      c2= it2.next();
      while(it1.hasNext())
      {
        c1=  it1.next();
        while(it2.hasNext() && ((Comparable)c1).compareTo(c2)>0)
        {
          c2 = it2.next();
        }
        if(c1.equals(c2))
          result.add(c1);
        if(!it2.hasNext() && ((Comparable)c1).compareTo(c2)>=0)
          break;
      }
    }
    return result;
  }

  /**
   *
   * @return a clone of this object
   */
  public SetExtent clone()
  {
	SetExtent newObj= new SetExtent();
	newObj.addAll(this);
	return newObj;
  }

 // public String toString() {

 // }

}
