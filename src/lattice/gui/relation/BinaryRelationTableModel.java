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

package lattice.gui.relation;
import javax.swing.event.TableModelEvent;

import lattice.util.concept.AbstractFormalAttributeValue;
import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.DefaultFormalObject;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalAttributeValue;
import lattice.util.concept.FormalObject;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.RelationBuilder;

/**
 * @author Mr ROUME
 * 
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class BinaryRelationTableModel extends AbstractRelationTableModel {

	private MatrixBinaryRelationBuilder absRel;

    /**
	 * Constructor for fdsTableModel.
	 */
	public BinaryRelationTableModel(MatrixBinaryRelationBuilder br) {
        absRel = br;
	}

	public void setValueAt(Object aValue, int rowIdx, int colIdx) {
		try {
			if (rowIdx == 0 && colIdx == 0) {
				absRel.setName((String) aValue);
			}
			if (rowIdx == 0 && colIdx > 0) {
				absRel.replaceAttribute(colIdx - 1,
					new DefaultFormalAttribute((String) aValue));
			}
			if (rowIdx > 0 && colIdx == 0) {
				absRel.replaceObject(rowIdx - 1,
					new DefaultFormalObject((String) aValue));
			}
			if (rowIdx > 0 && colIdx > 0) {
				absRel.setRelation(rowIdx - 1, colIdx - 1, !aValue.equals("0"));
			}
		} catch (BadInputDataException bide) {
			message = bide.getMessage();
			fireTableChanged(new TableModelEvent(this));
		}

	}

	public void revertRelation(int rowIdx, int colIdx) {
		if (rowIdx > 0 && colIdx > 0)
			absRel.revertRelation(rowIdx  - 1, colIdx - 1);
	}

    /**
     * @see TableModel#getRowCount()
     */
    public int getRowCount() {
    	return absRel.getObjectsNumber() + 1;
    }

    /**
     * @see TableModel#getColumnCount()
     */
    public int getColumnCount() {
    	return absRel.getAttributesNumber() + 1;
    }

    /**
    * @see TableModel#getValueAt(int, int)
    */
    public Object getValueAt(int rowIdx, int colIdx) {
    	if (rowIdx == 0 && colIdx == 0)
    		return absRel.getName();
    	if (rowIdx == 0 && colIdx > 0)
    		return absRel.getFormalAttribute(colIdx - 1);
    	if (rowIdx > 0 && colIdx == 0)
    		return absRel.getFormalObject(rowIdx - 1);
        AbstractFormalAttributeValue afav;
    	afav = absRel.getRelation(rowIdx - 1,colIdx - 1);
        if (!(afav instanceof FormalAttributeValue)) {
            return afav;
        }
        FormalAttributeValue fav = (FormalAttributeValue) afav;
        if (fav.isFalse()) {
            return "0";
        }
        return "X";
    }


}