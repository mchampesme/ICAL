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

package lattice.gui.graph.Example;

import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.Vector;

import lattice.util.concept.Concept;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.Node;

/**
 * <p>Title: Galicia</p>
 * <p>Description: Galois Lattice Interactive Constructor</p>
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: University of Montreal</p>
 * @author David Grosser
 * @version 1.0
 */

public class ExampleNode implements ConceptNode {

  List<Node<Concept>> children = new Vector<Node<Concept>>();
  Set<Node<Concept>> parents = new TreeSet<Node<Concept>>();
  Integer id = null;
  String label = null;

  public ExampleNode(String label) {
    this.label = label;
  }

  public ExampleNode(Integer id) {
    this.id = id;
  }

  public ExampleNode(int id) {
     this.id = new Integer(id);
  }
// Implements Node
 
  public void removeParent(ConceptNode n) {;}
  public void removeChild(ConceptNode n) {;}

  public Integer getId() {
    return id;
  }

  public List getChildren() {
    return children;
  }

  public Set getParents() {
    return parents;
  }

  public String toString() {
    if(getId() != null) return getId().toString();
    else return label;
  }

  public boolean getVisited() {
    return false;
  }

  public void setVisited(boolean b) {;}

// Fin implements Node
  public void addChild(ConceptNode n) {
    children.add(n);
  }

  public void addParent(ConceptNode n) {
    parents.add(n);
  }

  // Pour les parcours en largeur
	private int degre=-1;
	
	public void setDegre(int d){
		degre=d;
	}

	public int getDegre(){
		return degre; 
	}

	public void resetDegre(){
		degre=-1;
		for(Iterator it=getChildren().iterator();it.hasNext();){
			((ConceptNode)it.next()).resetDegre();
		}
	}

	/* (non-Javadoc)
	 * @see lattice.util.Node#linkNodeToUpperCovers(lattice.util.Node)
	 */
	public void linkNodeToUpperCovers(ConceptNode n2) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see lattice.util.Node#linkToUpperCovers(lattice.util.Node)
	 */
	public void linkToUpperCovers(ConceptNode n2) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see lattice.util.ConceptNode#equals(java.lang.Comparable)
	 */
	public boolean equals(Comparable o) {
		// TODO Auto-generated method stub
		return false;
	}

	/* (non-Javadoc)
	 * @see lattice.util.Node#getContent()
	 */
	public Concept getContent() {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see lattice.util.Node#addChild(lattice.util.Node)
	 */
	public void addChild(Node N) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see lattice.util.Node#removeChild(lattice.util.Node)
	 */
	public void removeChild(Node N) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see lattice.util.Node#addParent(lattice.util.Node)
	 */
	public void addParent(Node N) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see lattice.util.Node#removeParent(lattice.util.Node)
	 */
	public void removeParent(Node N) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see lattice.util.Node#linkNodeToUpperCovers(lattice.util.Node)
	 */
	public void linkNodeToUpperCovers(Node n2) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see lattice.util.Node#linkToUpperCovers(lattice.util.Node)
	 */
	public void linkToUpperCovers(Node n2) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see lattice.util.ConceptNode#equals(lattice.util.ConceptNode)
	 */
	public boolean equals(ConceptNode o) {
		// TODO Auto-generated method stub
		return false;
	}

	/* (non-Javadoc)
	 * @see lattice.util.Node#equals(lattice.util.Node)
	 */
	public boolean equals(Node n) {
		// TODO Auto-generated method stub
		return false;
	}


}