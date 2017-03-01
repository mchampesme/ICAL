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
import java.awt.Color;
import java.awt.event.ActionEvent;

import javax.swing.JOptionPane;
import javax.swing.JTable;
import javax.swing.event.TableModelEvent;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.TableCellRenderer;
import javax.swing.table.TableModel;

import lattice.util.relation.RelationBuilder;

/**
 * @author Mr ROUME
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public abstract class AbstractRelationTableEditor
	extends JTable {

	protected Color bGroundCell = new Color(200, 200, 220);

	/**
	 * Constructor for fdsTable.
	 * @param arg0
	 */
	public AbstractRelationTableEditor(TableModel arg0) {
		super(arg0);

		setAutoResizeMode(JTable.AUTO_RESIZE_OFF);
		setCellSelectionEnabled(true);
		setColumnSelectionAllowed(false);
		setRowSelectionAllowed(false);

	}

    
	public abstract void setModelFromRelation(RelationBuilder absRel);

	public TableCellRenderer getCellRenderer(int rowId, int colId) {
		DefaultTableCellRenderer dtcr =
			(DefaultTableCellRenderer) super.getCellRenderer(rowId, colId);
		if ((rowId == 0 && colId > 0)
			|| (rowId > 0 && colId == 0)
			|| (rowId > 0
				&& colId > 0
				&& !getValueAt(rowId, colId).toString().equals("0")))
			dtcr.setBackground(bGroundCell);
		else
			dtcr.setBackground(Color.white);
		return dtcr;
	}

	public void tableChanged(TableModelEvent tme) {
		super.tableChanged(tme);
		if (!((AbstractRelationTableModel) getModel())
			.getMessage()
			.equals("Ouverture")) {
			JOptionPane.showMessageDialog(
				this,
				((BinaryRelationTableModel) getModel()).getMessage());
		}
		//System.out.println("Coucou");
	}

	public abstract void queryNewInputRelationValue(int rowId, int colId);

	// Gestionnaire des click sur MenuItem
	public void actionPerformed(ActionEvent ae) {
		int rowIdx = getSelectedRow();
		int colIdx = getSelectedColumn();

	}

}