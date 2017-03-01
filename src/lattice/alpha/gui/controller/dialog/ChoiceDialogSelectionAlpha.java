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
package lattice.alpha.gui.controller.dialog;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.List;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.ListSelectionModel;


/**
 * 
 */
public class ChoiceDialogSelectionAlpha extends JDialog implements
        ActionListener {

    /**
     * 
     */
    private static final long serialVersionUID = -4163367864825738154L;

    public static int SELECT = 1;

    public static int CANCELLED = -1;

    private int status = 0;

    public JList<Object> listView = new JList<Object>();

    private JButton cancelButton = new JButton("Cancel");

    private JButton selectButton = new JButton("Select");

    private Object data = null;

    private Component controller = null;

    /**
     * @throws java.awt.HeadlessException
     */
    public ChoiceDialogSelectionAlpha(Component controler,
                                      List<Object> latticeRelationList, String message) {
        this.controller = controler;

        listView.setListData(latticeRelationList.toArray());
        listView
                .setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);

        JPanel globalPanel = new JPanel(new BorderLayout());

        // Set the centerPanel: a message and the selection list
        JPanel centerPanel = new JPanel(new BorderLayout());
        
        JLabel msgLabel = new JLabel(message);
        centerPanel.add(msgLabel, BorderLayout.NORTH);
        
        JScrollPane scp = new JScrollPane(
                                          listView,
                                          JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
                                          JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
        centerPanel.add(scp, BorderLayout.CENTER);
        globalPanel.add(centerPanel, BorderLayout.CENTER);

        // Set the south panel: the select and cancel buttons
        JPanel southPanel = new JPanel(new FlowLayout());
        southPanel.add(selectButton);
        southPanel.add(cancelButton);
        selectButton.addActionListener(this);
        cancelButton.addActionListener(this);
        globalPanel.add(southPanel, BorderLayout.SOUTH);

        // Global settings of the panel
        setContentPane(globalPanel);
        setTitle("Data Selection");
        setSize(400, 400);
        setResizable(true);
        setModal(true);
    }

    /**
     * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
     */
    public void actionPerformed(ActionEvent event) {
        data = null;
        if (!listView.isSelectionEmpty()) {
            data = listView.getSelectedValues();
        } 

        status = SELECT;
        dispose();

        if (event.getSource() == cancelButton) {
            status = CANCELLED;
            dispose();
        }
    }

    public void askParameter() {
        if (controller != null)
            controller.setEnabled(false);
        setVisible(true);
        if (controller != null)
            controller.setEnabled(true);
    }

    public Object getData() {
        return data;
    }

    public int getAction() {
        return status;
    }
}
