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
 * Created on Dec 25, 2004
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package lattice.io.rasterizer;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.StringWriter;
import java.io.Writer;

import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.filechooser.FileFilter;

import org.apache.batik.dom.GenericDOMImplementation;
import org.apache.batik.svggen.SVGGraphics2D;
import org.apache.batik.svggen.SVGGraphics2DIOException;
import org.w3c.dom.DOMImplementation;
import org.w3c.dom.Document;

/**
 * @author-1 rouanehm (Amine Med Rouane Hacene, UdeM)
 * @author-2 Christian pagé (UQAM)
 * Saturday, December 25, 2004
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public final class SVGWriter  {

	public SVGWriter() {}

	public static void capture(JPanel panel) {
		// see http://xml.apache.org/batik/svggen.html#whatIsIt
	    DOMImplementation domImpl = GenericDOMImplementation.getDOMImplementation();
	    Document document = domImpl.createDocument(null, "svg", null);
	    SVGGraphics2D svgGenerator = new SVGGraphics2D(document);
	    svgGenerator.setSVGCanvasSize(panel.getSize());
	    panel.paint(svgGenerator);
	    try {	      
	    	final JFileChooser saveDialogBox = new JFileChooser();
	    	saveDialogBox.setDialogTitle("Galicia lattice graph vectorinzing...");
	    	saveDialogBox.setDragEnabled(true);
	    	saveDialogBox.setFileSelectionMode(javax.swing.JFileChooser.FILES_AND_DIRECTORIES);
	    	saveDialogBox.setFileFilter(new FileFilter() {
	    	    public boolean accept(java.io.File file) {
	    		return file.isDirectory() || file.getName().endsWith(".svg");
	    	    }
	    	    public String getDescription() { return "*.svg"; }
	    	});
	    	int returnVal = saveDialogBox.showSaveDialog(panel);
	    	if (returnVal == JFileChooser.APPROVE_OPTION) {
	            File svgFile = saveDialogBox.getSelectedFile();	 	            
	            FileOutputStream outfile = new FileOutputStream(svgFile);
				Writer out = new OutputStreamWriter(outfile, "UTF-8");	            
		    	svgGenerator.stream(out,true);  
	             
	        } else {
	        	JOptionPane.showMessageDialog(panel,"Save command cancelled by user."+System.err.toString());
	        }	    	 
	    }
	    catch (Exception e) {
	    	JOptionPane.showMessageDialog(panel,"System error "+System.err.toString());
	    	e.printStackTrace( );
	    }
	  }

	public static void captureInFile(JPanel panel,File svgFile) {
	    DOMImplementation domImpl = GenericDOMImplementation.getDOMImplementation();
	    Document document = domImpl.createDocument(null, "svg", null);
	    SVGGraphics2D svgGenerator = new SVGGraphics2D(document);
	    svgGenerator.setSVGCanvasSize(panel.getSize());
	    panel.paint(svgGenerator);	 
		try {
			FileOutputStream outfile = new FileOutputStream(svgFile);
			Writer out = new OutputStreamWriter(outfile, "UTF-8");
			svgGenerator.stream(out,true);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	  }
	
	public static String getSVGData(JPanel panel) {
	    DOMImplementation domImpl = GenericDOMImplementation.getDOMImplementation();
	    Document document = domImpl.createDocument(null, "svg", null);
	    SVGGraphics2D svgGenerator = new SVGGraphics2D(document);
	    svgGenerator.setSVGCanvasSize(panel.getSize());
	    panel.paint(svgGenerator);
	    Writer out = new StringWriter(); 
	    try {
			svgGenerator.stream(out,true);
		} catch (SVGGraphics2DIOException e) {
			JOptionPane.showMessageDialog(panel,"SVG IO exception "+System.err.toString());
			e.printStackTrace();
		}    
		return out.toString();
	  }	
}
