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
 * Amine Med Rouane Hacene, UdeM
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package lattice.io.rasterizer;

import java.io.*;
import javax.swing.JFileChooser;
import javax.swing.filechooser.FileFilter;
import javax.swing.JPanel;
import javax.swing.JOptionPane;
//import org.apache.batik.transcoder.image.JPEGTranscoder;
//import org.apache.batik.transcoder.TranscoderInput;
//import org.apache.batik.transcoder.TranscoderOutput;

/**
 * @author rouanehm
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class JPEGWriter {	    
	   
	public static void capture(JPanel panel) throws Exception {
		try {	      
	    	final JFileChooser saveDialogBox = new JFileChooser();
	    	saveDialogBox.setDialogTitle("Galicia lattice graph PDF export...");
	    	saveDialogBox.setDragEnabled(true);
	    	saveDialogBox.setFileSelectionMode(javax.swing.JFileChooser.FILES_AND_DIRECTORIES);
	    	saveDialogBox.setFileFilter(new FileFilter() {
	    	    public boolean accept(java.io.File file) {
	    		return file.isDirectory() || file.getName().endsWith(".jpg");
	    	    }
	    	    public String getDescription() { return "*.jpg"; }
	    	});
	    	int returnVal = saveDialogBox.showSaveDialog(panel);
	    	if (returnVal == JFileChooser.APPROVE_OPTION) {
	    		File jpegFile = saveDialogBox.getSelectedFile();
	    		jpegFile.createNewFile();
		        // create a JPEG transcoder
		    
	    		//
	    	/*	JPEGTranscoder t = new JPEGTranscoder();
	    		t.addTranscodingHint(JPEGTranscoder.KEY_QUALITY,new Float(.8));
	    		Rectangle aoi = new Rectangle();   	
	    		t.addTranscodingHint(JPEGTranscoder.KEY_WIDTH,new Float(aoi.width));
	    		t.addTranscodingHint(JPEGTranscoder.KEY_HEIGHT,new Float(aoi.height));
	    		t.addTranscodingHint(JPEGTranscoder.KEY_AOI, panel.bounds());
	    		
	    		String svgFilename = "buffer.svg";
		        File svgFile = new File(svgFilename);
		        SVGWriter.captureInFile(panel,svgFile);			        			        
		        String svgURI = svgFile.toURL().toString();
		        	    		
	    		//TranscoderInput input = new TranscoderInput(svgURI);
	    		OutputStream ostream = new FileOutputStream(jpegFile);
	    		//TranscoderOutput output = new TranscoderOutput(ostream);
	    		//t.transcode(input, output);
	    		ostream.flush();
	    		ostream.close();
	    		// free file
			    //svgFile.delete();*/
	    	} else {
	        	//JOptionPane.showMessageDialog(panel,"Save command cancelled by user."+System.err.toString());
	        }	    	 
	    }
	    catch (Exception e) {
	    	JOptionPane.showMessageDialog(panel,"System error "+System.err.toString());
	    	e.printStackTrace( );
	    }
    	
	    }
}