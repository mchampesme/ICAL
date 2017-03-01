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
 * Created on 2004-08-03
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package lattice.util.structure;

import java.util.List;
import java.util.Set;

/**
 * @author rouanehm
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public interface Node<E> {
	/**
	 *
	 * @return a ConceptImp
	 */
	public E getContent();

	/**
	 *
	 * @return Id
	 */
	public Integer getId();

	/**
	 *
	 * @return a List
	 */
	public List<Node<E>> getChildren();
  
	public void addChild(Node<E> n);

	public void removeChild(Node<E> n);

	/**
	 *
	 * @return a Set
	 */
	public Set<Node<E>> getParents();

	public void addParent(Node<E> n);

	public void removeParent(Node<E> n);

	/**
	 *
	 * @return
	 */
	public boolean getVisited();

	/**
	 *
	 * @param b
	 */
	public void setVisited(boolean b);
  

   //Pour faire un parcour suivant une extension lineaire  
	public void setDegre(int d);
	public int getDegre();
	public void resetDegre();
  
	  //-------------------------------------------------
	  //Méthodes retirées de CompleteConceptLattice
	
	public void linkToUpperCovers( Node<E> n);

	
  
	  //-------------------------------------------------

}
