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
 * Created on 2004-08-16
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package lattice.algorithm.rca;

import lattice.util.concept.Concept;
import lattice.util.concept.FormalAttribute;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.Node;

/**
 * @author rouanehm
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class RelationalAttributeData{
	private FormalAttribute 		fa;
	private String 		relationName;
	private String 		contextName;
	private Integer 	nodeID;
	private Node<Concept> conceptNode;
	
	public RelationalAttributeData(FormalAttribute fa,String rn, String ctxn,Integer id){
		this.fa=fa; relationName=rn; contextName=ctxn; nodeID=id; conceptNode=null;}
	
	public String getRelAttrName(){ return fa.getName(); }
	public String getRelationName(){ return relationName; }
	public String getContextName(){ return contextName; }
	public Integer getNodeID(){ return nodeID; }
	public Node<Concept> getConceptNode(){ return conceptNode; }
	public FormalAttribute getFormalAttribute(){ return fa; }
	public void setConceptNode(Node<Concept> cn){ conceptNode=cn;}
	/**
	 * @param string
	 */
	public void setContextName(String ctxName) { contextName = ctxName; }	
}
