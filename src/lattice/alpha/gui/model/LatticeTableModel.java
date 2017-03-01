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
package lattice.alpha.gui.model;

import java.util.ArrayList;
import java.util.List;

import javax.swing.table.AbstractTableModel;

import lattice.util.structure.CompleteConceptLattice;

/**
 * @author marc
 *
 */
public class LatticeTableModel extends AbstractTableModel {

    /**
     * 
     */
    private static final long serialVersionUID = 250197409972172413L;
    
    private List<LatticeModel> latticeList;
    
    private String[] columnNames = {"Lattice", "alpha", "generators", "# of nodes"};

    public LatticeTableModel() {
        latticeList = new ArrayList<LatticeModel>();
    }

    public LatticeTableModel(List<LatticeModel> latticeList) {
        this.latticeList = latticeList;
    }
    
    public String getColumnName(int col) {
        return columnNames[col];
    }

    public Class<? extends Object> getColumnClass(int col) {
        return getValueAt(0, col).getClass();
    }

    /**
     * @see javax.swing.table.TableModel#getRowCount()
     */
    public int getRowCount() {
        return latticeList.size();
    }

    /**
     * @see javax.swing.table.TableModel#getColumnCount()
     */
    public int getColumnCount() {
         return columnNames.length;
    }

    /**
     * @see javax.swing.table.TableModel#getValueAt(int, int)
     */
    public Object getValueAt(int rowIndex, int columnIndex) {
        LatticeModel lattice = getLatticeModel(rowIndex);
        switch (columnIndex) {
            case 0: return lattice.getDescription();
            case 1: return lattice.getAlphaValue();
            case 2: return lattice.hasGenerators();
            case 3: return lattice.getNumberOfNodes();
        }
        return null;
    }

    public LatticeModel getLatticeModel(int rowIndex) {
        return latticeList.get(rowIndex);
    }
    
    public void addLattice(CompleteConceptLattice lattice, double alphaValue) {
        int updatedRow = latticeList.size();
        latticeList.add(new LatticeModel(lattice, alphaValue));
        fireTableRowsInserted(updatedRow, updatedRow); 
    }
    
    public List<LatticeModel> getLatticeSubList(int[] rows) {
        List<LatticeModel> latticeSubList = new ArrayList<LatticeModel>(rows.length);
        for (int i = 0; i < rows.length; i++) {
            latticeSubList.add(getLatticeModel(rows[i]));
        }
        return latticeSubList;
    }
}
