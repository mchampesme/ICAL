package lattice.alpha.gui;

/*
 * A 1.4 example that uses the following files:
 *    LatticeTreeModel.java
 *    Person.java
 *
 * Based on an example provided by tutorial reader Olivier Berlanger.
 */
import javax.swing.ButtonGroup;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JScrollPane;
import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import lattice.util.structure.ConceptNode;

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
public class LatticeBrowser extends JPanel 
                              implements ActionListener {
    /**
     * 
     */
    private static final long serialVersionUID = 5727432718610610373L;
    private LatticeTree tree;
    private static String SHOW_ANCESTOR_CMD = "showAncestor";

    public LatticeBrowser(LatticeTreeNode top) {
        super(new BorderLayout());
        
        //Construct the panel with the toggle buttons.
        JRadioButton showDescendant = 
                new JRadioButton("Show descendants", true);
        final JRadioButton showAncestor = 
                new JRadioButton("Show ancestors");
        ButtonGroup bGroup = new ButtonGroup();
        bGroup.add(showDescendant);
        bGroup.add(showAncestor);
        showDescendant.addActionListener(this);
        showAncestor.addActionListener(this);
        showAncestor.setActionCommand(SHOW_ANCESTOR_CMD);
        JPanel buttonPanel = new JPanel();
        buttonPanel.add(showDescendant);
        buttonPanel.add(showAncestor);

        //Construct the tree.
        tree = new LatticeTree(top);
        JScrollPane scrollPane = new JScrollPane(tree);
        scrollPane.setPreferredSize(new Dimension(200, 200));

        //Add everything to this panel.
        add(buttonPanel, BorderLayout.PAGE_START);
        add(scrollPane, BorderLayout.CENTER);
    }

    /** 
     * Required by the ActionListener interface.
     * Handle events on the showDescendant and
     * showAncestore buttons. 
     */
    public void actionPerformed(ActionEvent ae) {
        if (ae.getActionCommand() == SHOW_ANCESTOR_CMD) {
            tree.showAncestor(true);
        } else {
            tree.showAncestor(false);
        }
    }
    
    /**
     * Create the GUI and show it.  For thread safety,
     * this method should be invoked from the
     * event-dispatching thread.
     */
    public static void createAndShowGUI(String windowTitle, ConceptNode top) {
        //Make sure we have nice window decorations.
        JFrame.setDefaultLookAndFeelDecorated(true);

        //Create and set up the window.
        JFrame frame = new JFrame(windowTitle);
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

        //Create and set up the content pane.
        LatticeBrowser newContentPane = new LatticeBrowser(new LatticeTreeNode(top));
        newContentPane.setOpaque(true); //content panes must be opaque
        frame.setContentPane(newContentPane);

        //Display the window.
        frame.pack();
        frame.setVisible(true);
    }

    public static void main(String[] args) {
        //Schedule a job for the event-dispatching thread:
        //creating and showing this application's GUI.
        javax.swing.SwingUtilities.invokeLater(new Runnable() {
            public void run() {
                createAndShowGUI("LatticeBrowser", null);
            }
        });
    }
}
