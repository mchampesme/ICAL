package lattice.alpha.gui.model;

import java.util.ArrayList;
import java.util.List;

import javax.swing.table.AbstractTableModel;

import lattice.util.relation.RelationBuilder;

/*
 *  Copyright LIPN
 *  contributor(s) : Marc Champesme (2006) marc.champesme@lipn.univ-paris13.fr
 *  
 *  This software is a computer program whose purpose is the Incremental construction of Alpha lattices.
 *  
 *  This software is governed by the CeCILL license under French law and
 *  abiding by the rules of distribution of free software.  You can  use, 
 *  modify and/ or redistribute the software under the terms of the CeCILL
 *  license as circulated by CEA, CNRS and INRIA at the following URL
 *  "http://www.cecill.info". 
 *  
 *  As a counterpart to the access to the source code and  rights to copy,
 *  modify and redistribute granted by the license, users are provided only
 *  with a limited warranty  and the software's author,  the holder of the
 *  economic rights,  and the successive licensors  have only  limited
 *  liability. 
 *  
 *  In this respect, the user's attention is drawn to the risks associated
 *  with loading,  using,  modifying and/or developing or reproducing the
 *  software by the user in light of its specific status of free software,
 *  that may mean  that it is complicated to manipulate,  and  that  also
 *  therefore means  that it is reserved for developers  and  experienced
 *  professionals having in-depth computer knowledge. Users are therefore
 *  encouraged to load and test the software's suitability as regards their
 *  requirements in conditions enabling the security of their systems and/or 
 *  data to be ensured and,  more generally, to use and operate it in the 
 *  same conditions as regards security. 
 *  
 *  The fact that you are presently reading this means that you have had
 *  knowledge of the CeCILL license and that you accept its terms.
 */
public class RelationTableModel extends AbstractTableModel {
    /**
     * 
     */
    private static final long serialVersionUID = 6169965354009695369L;
    private List<RelationModel> relationList;
    private String[] columnNames = {"Relation", "# of attributes", "# of objects"};

    public RelationTableModel() {
        relationList = new ArrayList<RelationModel>();
    }
    
    public RelationTableModel(List<RelationModel> relationList) {
        this.relationList = relationList;
    }
    
    public String getColumnName(int col) {
        return columnNames[col];
    }

    public Class<? extends Object> getColumnClass(int col) {
        return getValueAt(0, col).getClass();
    }

    public int getRowCount() {
        return relationList.size();
    }

    public int getColumnCount() {
        return columnNames.length;
    }

    public Object getValueAt(int rowIndex, int columnIndex) {
        RelationModel relation = relationList.get(rowIndex);
        switch (columnIndex) {
        case 0: return relation.getDescription();
        case 1: return relation.getNumberOfAttributes();
        case 2: return relation.getNumberOfObjects();
        }
        return null;
    }

    public RelationModel getRelationModel(int rowIndex) {
        return relationList.get(rowIndex);
    }
    
    public void addRelation(RelationBuilder relation) {
        int updatedRow = relationList.size();
        relationList.add(new RelationModel(relation));
        fireTableRowsInserted(updatedRow, updatedRow); 
    }
    
    public List<RelationModel> getRelationSubList(int[] rows) {
        List<RelationModel> relationSubList = new ArrayList<RelationModel>(rows.length);
        for (int i = 0; i < rows.length; i++) {
            relationSubList.add(getRelationModel(rows[i]));
        }
        return relationSubList;
    }

}
