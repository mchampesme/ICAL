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
package lattice.alpha.gui.view;

import java.awt.BorderLayout;
import java.util.List;

import javax.swing.BorderFactory;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.ListSelectionModel;

import lattice.alpha.gui.model.LatticeModel;
import lattice.alpha.gui.model.LatticeTableModel;

public class LatticeSelectionPanel extends JPanel {
    /**
     * 
     */
    private static final long serialVersionUID = 4500093173713585118L;
    
    private LatticeTableModel latticeTableModel;

    private JTable table;
    
    
    public LatticeSelectionPanel(String message, LatticeTableModel lattices) {
        super(new BorderLayout(10, 10));
        latticeTableModel = lattices;

        // Set the message on top of the table
        JLabel msgLabel = new JLabel(message);
        add(msgLabel, BorderLayout.NORTH);
        
        table = new JTable(latticeTableModel);
        table.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);
        // Put scrollbars around the table
        JScrollPane scp = new JScrollPane(table);
        
        setBorder(BorderFactory.createEmptyBorder(20, 20, 20, 20));
        add(scp, BorderLayout.CENTER);
    }
    
    public List<LatticeModel> getSelectedLattices() {
        int[] rows = table.getSelectedRows();
        return latticeTableModel.getLatticeSubList(rows);
    }
}
