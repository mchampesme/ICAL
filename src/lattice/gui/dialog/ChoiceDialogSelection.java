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
 * Created on 9 juil. 2003
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package lattice.gui.dialog;

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Vector;

import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.ListSelectionModel;

import lattice.gui.OpenFileFrame;
import lattice.gui.RelationalContextEditor;
 
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.RelationalContextFamily;

/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ChoiceDialogSelection
        extends JDialog
        implements ActionListener {

      public static int SELECT = 1;
      public static int CANCELLED = -1;
      private int Status = 0;

      private JList theList = new JList();
      Vector listAll = new Vector();
      Vector listBin = new Vector();
      Vector listMvc = new Vector();
      Vector listLat = new Vector();

      private JButton cancelButton = new JButton("Cancel");
      private JButton selectButton = new JButton("Select");

      private JComboBox combo = null;

      private Object data = null;
      private int typeOfExport = OpenFileFrame.FAMILY_DATA;

      private RelationalContextEditor controller = null;

      /**
       * @throws java.awt.HeadlessException
       */
      public ChoiceDialogSelection(RelationalContextFamily relCtx,
                                   RelationalContextEditor controler,
                                   String message) {
        super();

        this.controller = controler;

        for (int i = 0; i < relCtx.size(); i++) {
          listAll.add(relCtx.get(i));
        }
        theList.setListData(listAll);
        theList.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);

        JPanel panelGlob = new JPanel(new BorderLayout());

        JPanel panelNorth = new JPanel(new FlowLayout());

        JPanel panelCenter = new JPanel(new BorderLayout());
        JLabel lab2 = new JLabel(message);
        panelCenter.add(lab2, BorderLayout.NORTH);
        JScrollPane scp = new JScrollPane(theList,
                                          JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
                                          JScrollPane.
                                          HORIZONTAL_SCROLLBAR_AS_NEEDED);
        panelCenter.add(scp, BorderLayout.CENTER);
        panelGlob.add(panelCenter, BorderLayout.CENTER);

        JPanel panelSud = new JPanel(new FlowLayout());
        panelSud.add(selectButton);
        panelSud.add(cancelButton);
        selectButton.addActionListener(this);
        cancelButton.addActionListener(this);
        panelGlob.add(panelSud, BorderLayout.SOUTH);

        setContentPane(panelGlob);
        setTitle("Data Selection");
        setSize(400, 400);
        setResizable(false);
        setModal(true);
      }

      public ChoiceDialogSelection(RelationBuilder r, String t, String message1, String message2) {
        super();
        //this.controller = controller;

        if (t.equals("objects")) {
          typeOfExport = OpenFileFrame.OBJECTS_DATA;
          for (int i = 0; i < r.getObjectsNumber(); i++) {
            listAll.add((FormalObject) r.getObjects().get(i));
          }
          theList.setListData(listAll);
          theList.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);

          JPanel panelGlob = new JPanel(new BorderLayout());

          JPanel panelNorth = new JPanel(new FlowLayout());

          JPanel panelCenter = new JPanel(new BorderLayout());
          JLabel lab2 = new JLabel(message1);
          panelNorth.add(lab2);
          lab2 = new JLabel(message2);
          panelCenter.add(lab2, BorderLayout.NORTH);
          JScrollPane scp = new JScrollPane(theList,
                                            JScrollPane.
                                            VERTICAL_SCROLLBAR_AS_NEEDED,
                                            JScrollPane.
                                            HORIZONTAL_SCROLLBAR_AS_NEEDED);
          panelCenter.add(scp, BorderLayout.CENTER);
          panelGlob.add(panelNorth, BorderLayout.NORTH);
          panelGlob.add(panelCenter, BorderLayout.CENTER);

          JPanel panelSud = new JPanel(new FlowLayout());
          panelSud.add(selectButton);
          panelSud.add(cancelButton);
          selectButton.addActionListener(this);
          cancelButton.addActionListener(this);
          panelGlob.add(panelSud, BorderLayout.SOUTH);

          setContentPane(panelGlob);
          setTitle("Data Selection");
          setSize(400, 400);
          setResizable(false);
          setModal(true);
        }
        else {
          typeOfExport = OpenFileFrame.ATTRIBUTES_DATA;
          for (int i = 0; i < r.getAttributesNumber(); i++) {
            listAll.add((FormalAttribute) r.getAttributes().get(i));
          }
          theList.setListData(listAll);
          theList.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);

          JPanel panelGlob = new JPanel(new BorderLayout());

          JPanel panelNorth = new JPanel(new FlowLayout());

          JPanel panelCenter = new JPanel(new BorderLayout());
          JLabel lab2 = new JLabel(message1);
          panelNorth.add(lab2);
          lab2 = new JLabel(message2);
          panelCenter.add(lab2, BorderLayout.NORTH);
          JScrollPane scp = new JScrollPane(theList,
                                            JScrollPane.
                                            VERTICAL_SCROLLBAR_AS_NEEDED,
                                            JScrollPane.
                                            HORIZONTAL_SCROLLBAR_AS_NEEDED);
          panelCenter.add(scp, BorderLayout.CENTER);
          panelGlob.add(panelNorth, BorderLayout.NORTH);
          panelGlob.add(panelCenter, BorderLayout.CENTER);

          JPanel panelSud = new JPanel(new FlowLayout());
          panelSud.add(selectButton);
          panelSud.add(cancelButton);
          selectButton.addActionListener(this);
          cancelButton.addActionListener(this);
          panelGlob.add(panelSud, BorderLayout.SOUTH);

          setContentPane(panelGlob);
          setTitle("Data Selection");
          setSize(400, 400);
          setResizable(false);
          setModal(true);
        }
      }

      /**
       * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
       */
      public void actionPerformed(ActionEvent arg0) {
        if (arg0.getSource() == selectButton) {
          if (getTypeOfExport() == OpenFileFrame.FAMILY_DATA) {
            RelationalContextFamily rc = new RelationalContextFamily();
            for (int i = 0; i < theList.getSelectedValues().length; i++) {
              rc.add( (RelationBuilder) theList.getSelectedValues()[i]);
            }
            data = rc;
          }
          else if (getTypeOfExport() == OpenFileFrame.OBJECTS_DATA) {
            if (!theList.isSelectionEmpty()) {
              Vector o = new Vector();
              for (int i = 0; i < theList.getSelectedValues().length; i++) {
                o.add( (FormalObject) theList.getSelectedValues()[i]);
              }
              data = o;
            }
            else {
              Status = SELECT;
              dispose();
            }
          }
          else if (getTypeOfExport() == OpenFileFrame.ATTRIBUTES_DATA){
            if (!theList.isSelectionEmpty()) {
            Vector a = new Vector();
            for (int i = 0; i < theList.getSelectedValues().length; i++) {
              a.add( (FormalAttribute) theList.getSelectedValues()[i]);
            }
            data = a;
          }
           else {
             Status = SELECT;
             dispose();
           }
         }
      Status = SELECT;
          dispose();
        }
        if (arg0.getSource() == cancelButton) {
          Status = CANCELLED;
          dispose();
        }
      }

      public void askParameter() {
        if (controller != null) controller.setEnabled(false);
        show();
        if (controller != null) controller.setEnabled(true);
      }

      public int getTypeOfExport() {
        return typeOfExport;
      }

      public Object getData() {
        return data;
      }

      public int getAction() {
        return Status;
      }
    }
