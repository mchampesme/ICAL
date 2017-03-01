/*
 ***********************************************************************
 * Copyright (C) 2005 The Galicia Team 
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
 * Created on 2005-02-01
 * Amine 
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package lattice.io.rasterizer;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseEvent;

import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPopupMenu;

import lattice.gui.graph.LatticeGraphViewer;

/**
 * @author rouanehm (Amine Med Rouane Hacene, UdeM)
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class TranscoderView implements ActionListener {

	LatticeGraphViewer lgvOwner;
	private JPopupMenu popupMenu = null;
	private JMenuItem svgRasterizer = null;
	private JMenuItem jpegRender = null;
	private JMenuItem pdfRender = null;
	private JMenuItem exit = null;
	
	public TranscoderView(LatticeGraphViewer lgvOwner){
		this.lgvOwner = lgvOwner;
		popupMenu = new JPopupMenu();
				
		svgRasterizer = new JMenuItem("SVG");
		svgRasterizer.addActionListener((ActionListener) this);
		svgRasterizer.setMnemonic('S');
		svgRasterizer.setAccelerator(
				javax.swing.KeyStroke.getKeyStroke(
					java.awt.event.KeyEvent.VK_V,
					java.awt.event.KeyEvent.CTRL_MASK,
					false));
		
		jpegRender = new JMenuItem("JPEG");
		jpegRender.addActionListener((ActionListener) this);
		jpegRender.setMnemonic('J');
		jpegRender.setAccelerator(
				javax.swing.KeyStroke.getKeyStroke(
					java.awt.event.KeyEvent.VK_J,
					java.awt.event.KeyEvent.CTRL_MASK,
					false));
		
		pdfRender = new JMenuItem("PDF");
		pdfRender.addActionListener((ActionListener) this);
		pdfRender.setMnemonic('P');
		pdfRender.setAccelerator(
				javax.swing.KeyStroke.getKeyStroke(
					java.awt.event.KeyEvent.VK_D,
					java.awt.event.KeyEvent.CTRL_MASK,
					false));	
		
		exit = new JMenuItem("Exit");
		exit.addActionListener((ActionListener) this);
		exit.setMnemonic('P');
		exit.setAccelerator(
				javax.swing.KeyStroke.getKeyStroke(
					java.awt.event.KeyEvent.VK_E,
					java.awt.event.KeyEvent.CTRL_MASK,
					false));	
				
		popupMenu.add(svgRasterizer);
		popupMenu.add(jpegRender);
		popupMenu.add(pdfRender);
		//popupMenu.addSeparator();
		//popupMenu.add(exit);
	}

	
	public void display(MouseEvent e){
		popupMenu.show(e.getComponent(),e.getX(),e.getY());
		}
	/* (non-Javadoc)
	 * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
	 */
	public void actionPerformed(ActionEvent ae) {
		//super.actionPerformed(ae);
		if (ae.getSource() == svgRasterizer) {
			SVGWriter.capture(lgvOwner);
		}
		if (ae.getSource() == jpegRender) {
			try {
				JPEGWriter.capture(lgvOwner);
			} catch (Exception e) {
				JOptionPane.showMessageDialog(lgvOwner,"JPEG export IO exception "+System.err.toString());	  		
				e.printStackTrace();
			}
		}
		if (ae.getSource() == pdfRender) {
			try {
				PDFWriter.capture(lgvOwner);
			} catch (Exception e) {
				JOptionPane.showMessageDialog(lgvOwner,"PDF export IO exception "+System.err.toString());
				e.printStackTrace();
			}
		}
		if (ae.getSource() == exit) {
			//popupMenu.close;
		}
	
	}//action performed	 
}
