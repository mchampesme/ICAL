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
 * Created on 12 juil. 2003
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package lattice.gui.controller;

import java.awt.event.ActionEvent;
import java.util.Vector;

import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;

import lattice.algorithm.Buvette;
import lattice.algorithm.GodinAD;
import lattice.algorithm.LatticeAlgorithm;
import lattice.algorithm.NextClosure;
import lattice.algorithm.NouReynaud;
import lattice.algorithm.ValtchevEtAl;
import lattice.algorithm.ValtchevEtAl2;
import lattice.algorithm.task.LatticeAlgorithmTask;
import lattice.gui.RelationalContextEditor;
import lattice.iceberg.algorithm.BordatIceberg;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.ScalingBinaryRelation;

/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class LatticeController extends AbstractController {

  private JMenu menuTrellit = null;
  private JMenuItem algoBordat = null;
  private JMenuItem algoGodinAD = null;
  private JMenuItem algoNouReynaud = null;
  private JMenuItem valNmissAlgo = null;
  private JMenuItem valNalAlgo = null;
  private JMenuItem ganterNextClosure = null;

  
  // Ajout pour Buvette : Mame Awa
  private JMenuItem buvette = null;

  private LatticeAlgorithmTask theTask=null;

  /**
   * @param rce
   */
  public LatticeController(RelationalContextEditor rce) {
    super(rce);
    initMenu();
    theTask=new LatticeAlgorithmTask(rce);
  }

  public void initMenu(){

    menuTrellit = new JMenu("Construct the lattice");
    menuTrellit.setMnemonic('T');

    // Les Items
    algoBordat = new JMenuItem("Bordat");
    algoBordat.setMnemonic('B');
    algoBordat.addActionListener(this);
    menuTrellit.add(algoBordat);

    valNmissAlgo = new JMenuItem("Valtchev & al. (2003)");
    valNmissAlgo.setMnemonic('V');
    valNmissAlgo.addActionListener(this);
    menuTrellit.add(valNmissAlgo);

    valNalAlgo = new JMenuItem("Valtchev & al. v2 (2003)");
    valNalAlgo.setMnemonic('A');
    valNalAlgo.addActionListener(this);
    menuTrellit.add(valNalAlgo);

    ganterNextClosure = new JMenuItem("Next Closure - Ganter");
    ganterNextClosure.setMnemonic('N');
    ganterNextClosure.addActionListener(this);
    menuTrellit.add(ganterNextClosure);

    
//  Ajout pour Buvette : Mame Awa
    buvette = new JMenuItem("Bottom-Up VErtical laTTice updatE");
    buvette.setMnemonic('B');
    buvette.addActionListener(this);
    menuTrellit.add(buvette);

    
    algoGodinAD = new JMenuItem("Godin (1995)");
    algoGodinAD.setMnemonic('G');
    algoGodinAD.addActionListener(this);
    menuTrellit.add(algoGodinAD);

    algoNouReynaud = new JMenuItem("Nourine Reynaud");
    algoNouReynaud.setMnemonic('N');
    algoNouReynaud.addActionListener(this);
    menuTrellit.add(algoNouReynaud);

  }

  public JMenu getMainMenu(){
    return menuTrellit;
  }


  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0) {
    if(arg0.getSource()==algoGodinAD){
      execAlgorithm(new GodinAD(((MatrixBinaryRelationBuilder)rce.getSelectedRelation())));
    }
    if(arg0.getSource()==algoBordat){
      execAlgorithm(new BordatIceberg(((MatrixBinaryRelationBuilder)rce.getSelectedRelation())));
    }
    if(arg0.getSource()==algoNouReynaud){
      execAlgorithm(new NouReynaud(((MatrixBinaryRelationBuilder)rce.getSelectedRelation())));
    }
    if(arg0.getSource()==valNmissAlgo){
      execAlgorithm(new ValtchevEtAl(((MatrixBinaryRelationBuilder)rce.getSelectedRelation())));
    }
    
//  Ajout pour Buvette : Mame Awa
    if(arg0.getSource()==buvette){
        execAlgorithm(new Buvette(((MatrixBinaryRelationBuilder)rce.getSelectedRelation())));
      }
    
	if(arg0.getSource()==ganterNextClosure){
        execAlgorithm(new NextClosure(((MatrixBinaryRelationBuilder)rce.getSelectedRelation())));
      }
	
    if(arg0.getSource()==valNalAlgo){
      boolean gens;
      JFrame frame = new JFrame();
      int choix = JOptionPane.showConfirmDialog(frame,
                                                "Do you want the generators to be calculated ?", "Generators Choice",
                                                JOptionPane.YES_NO_OPTION);
      if (choix == JOptionPane.YES_OPTION)
        gens = true;
      else
        gens = false;
      execAlgorithm(new ValtchevEtAl2((MatrixBinaryRelationBuilder)rce.getSelectedRelation(), gens));
    }
    rce.checkPossibleActions();
  }

  protected void execAlgorithm(LatticeAlgorithm algo){
    rce.setWorkOnRelation(algo.getBinaryRelation()); // marquer la relation 'On Use'
    Vector binRelOnUse=new Vector();
    binRelOnUse.add(algo.getBinaryRelation());
    theTask.setBinRelOnUse(binRelOnUse);
    theTask.setAlgo(algo);
    theTask.exec();
  }

  public void checkPossibleActions(){

    if(rce.getFamilyContexts().size()==0){
      menuTrellit.setEnabled(false);
      return;
    }

    RelationBuilder absRel=rce.getSelectedRelation();

    if(absRel instanceof MatrixBinaryRelationBuilder){
      menuTrellit.setEnabled(true);
      if(rce.isOnWork(absRel)) menuTrellit.setEnabled(false);
      return;
    }

    if(absRel instanceof ScalingBinaryRelation){
      menuTrellit.setEnabled(false);
      return;
    }

  }
}