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

import java.util.SortedSet;

/**
 * <p>Titre :  Galicia</p>
 * <p>Description : Interface de l'extension d'un concept</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : UniversitŽ de MontrŽal</p>
 * @author David Grosser
 * @version 1.0
 */
public interface Extent extends SortedSet<FormalObject> {
/**
 *
 * @param extent
 * @return
 */
  public Extent extentUnion(Extent extent);

  /**
   *
   * @param extent
   * @return
   */
  public Extent extentIntersection(Extent extent);

  /**
   *
   * @return
   */
  public Extent clone();
}
