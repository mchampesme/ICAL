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

package lattice.util.structure;

import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import lattice.util.concept.Concept;


/**
 *
 * <p>Titre : Lattice</p>
 * <p>Description : Manipulation des treillis</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : Université de Montréal</p>
 * @author David Grosser
 * @version 1.0
 */
public class ConceptLatticeIterator implements Iterator<Node<Concept>>
{

  private Iterator<Node<Concept>> iter;
  private Iterator<List<Node<Concept>>> it;

  /**
   *
   * @param index_level
   */
  public ConceptLatticeIterator(List<List<Node<Concept>>> index_level)
  {
    it  = index_level.iterator();

    if (it.hasNext())
      iter = it.next().iterator();
  }

  /**
   *
   * @return boolean value
   */
  public boolean hasNext() {
    if (iter.hasNext() ) return true;
    while( it.hasNext() ){
      iter = it.next().iterator();
      if( iter != null && iter.hasNext() ) return true;
    }
    return false;
  }

  /**
   *
   * @return next
   */
  public Node<Concept> next()
  {
    if(this.hasNext())
    {
      if (iter.hasNext())
        return iter.next();
      else
      {
        while(!iter.hasNext())
        {
          if( !it.hasNext())
            throw new NoSuchElementException();
        }
        return iter.next();
      }
    }
    else
      throw new NoSuchElementException();
  }

  /**
   *
   */
  public void remove()
  {
    throw new UnsupportedOperationException();
  }

}
