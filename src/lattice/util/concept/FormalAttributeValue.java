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


/**
 * @author Mr ROUME
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class FormalAttributeValue extends AbstractFormalAttributeValue {
    public static final  FormalAttributeValue TRUE = new FormalAttributeValue("X");
    public static final  FormalAttributeValue FALSE = new FormalAttributeValue("0");
	private static String emptyValue="0";
	private String theValue = emptyValue;
	/**
	 * Constructor for FormalAttributeValue.
	 */
	public FormalAttributeValue() {
		theValue=emptyValue;
	}

	/**
	 * Constructor for FormalAttributeValue.
	 */
	public FormalAttributeValue(String aValue) {
		theValue=aValue;
	}
			
	public boolean equals(Object o){
        if (!(o instanceof FormalAttributeValue)) {
            return false;
        }
        FormalAttributeValue other = (FormalAttributeValue) o;
		return theValue.equals(other.theValue);
	}

	public String toString(){
		return theValue.toString();
	}

	
	public int compareTo(Object o){
		return theValue.compareTo(((FormalAttributeValue)o).theValue);
	}
	
	public int hashCode() {
        return theValue.hashCode();
    }
    
    @Override
    public boolean isFalse() {
        return theValue.equals(emptyValue);
    }

    @Override
    public boolean isTrue() {
        return !isFalse();
    }
}
