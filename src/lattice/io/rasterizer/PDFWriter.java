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
 * Created on Dec 26, 2004
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package lattice.io.rasterizer;

/**
 * @author rouanehm (Amine Med Rouane Hacene, UdeM)
 * Sunday, December 26, 2004
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

import java.io.File;
import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.filechooser.FileFilter;



public class PDFWriter {
 
	    public static void capture(JPanel panel) throws Exception {
			// see http://xml.apache.org/batik/rasterizerTutorial.html
	    	try {	      
		    	final JFileChooser saveDialogBox = new JFileChooser();
		    	saveDialogBox.setDialogTitle("Galicia lattice graph PDF export...");
		    	saveDialogBox.setDragEnabled(true);
		    	saveDialogBox.setFileSelectionMode(javax.swing.JFileChooser.FILES_AND_DIRECTORIES);
		    	saveDialogBox.setFileFilter(new FileFilter() {
		    	    public boolean accept(java.io.File file) {
		    		return file.isDirectory() || file.getName().endsWith(".pdf");
		    	    }
		    	    public String getDescription() { return "*.pdf"; }
		    	});
		    	int returnVal = saveDialogBox.showSaveDialog(panel);
		    	if (returnVal == JFileChooser.APPROVE_OPTION) {
		    		File pdfFile = saveDialogBox.getSelectedFile();
		    		pdfFile.createNewFile();
			        // create a PDF transcoder
			      /*  PDFTranscoder t = new PDFTranscoder();			  
			        String svgFilename = "buffer.svg";
			        File svgFile = new File(svgFilename);
			        SVGWriter.captureInFile(panel,svgFile);			        			        
			        String svgURI = svgFile.toURL().toString();
			        TranscoderInput input = new TranscoderInput(svgURI);
			        // create the transcoder output
			        OutputStream ostream = new FileOutputStream(pdfFile);
			        TranscoderOutput output = new TranscoderOutput(ostream);
			     
			        //save the image
			        t.transcode(input, output);
			      //flush and close the stream then exit
			        ostream.flush();
			        ostream.close();
			        // free file
			        svgFile.delete();*/
		        } else {
		        	JOptionPane.showMessageDialog(panel,"Save command cancelled by user."+System.err.toString());
		        }	    	 
		    }
		    catch (Exception e) {
		    	JOptionPane.showMessageDialog(panel,"System error "+System.err.toString());
		    	e.printStackTrace( );
		    }
	    	
 	    }
}
