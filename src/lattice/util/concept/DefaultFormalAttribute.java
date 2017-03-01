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
import java.util.Vector;

import lattice.util.relation.MatrixBinaryRelationBuilder;

/**
 * @author Mr ROUME
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class DefaultFormalAttribute implements FormalAttribute {

	protected String name;
	/**
	 * Constructor for FormalAttribute.
	 */
	public DefaultFormalAttribute(String aName) {
		super();
		name=aName;
	}

	public String toString(){
		return name.toString();
	}

	public boolean equals(Object o){
		return name.equals(((DefaultFormalAttribute)o).name);
	}

	public int compareTo(Object o){
		return name.compareTo(((DefaultFormalAttribute)o).name);		
	}
	
	public String getName(){
		return name;
	}

	public void setName(String aName){
		name=aName;
	}

	public int hashCode(){
		return toString().hashCode();
	}
	
	// --- The Folowing MUST DISAPEAR do NOT USE !!! 
	protected TreeSet extension; // représentation creuse de l'extension de l'attribut (par indice)
	public void initExtension(Extent E,MatrixBinaryRelationBuilder bR){
		extension = new TreeSet();
		for(Iterator it=E.iterator(); it.hasNext(); ) 
			extension.add(new Integer(bR.getObjects().indexOf(it.next())));
	}

	
	public int calculSupport() {
		return extension.size();
	}
	
	public TreeSet getExtension() {
		return extension;
	}

/**
	* Créé un nouveau motif qui est l'intersection de this avec m
*/
	public TreeSet intersection(TreeSet m) {
		TreeSet t = new TreeSet();
		Integer i = null;
		for(Iterator it = m.iterator(); it.hasNext() ;) {
			i = (Integer) it.next();
			if(extension.contains(i)) t.add(i);
		}
		return t;
	}

}
