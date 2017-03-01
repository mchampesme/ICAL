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
 * Created on 2004-07-01
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package lattice.io;

import java.io.Reader;
import org.xml.sax.InputSource;

import lattice.io.xmigateway.RcfBuilder;
import lattice.io.xmigateway.XmiData;
import lattice.io.xmigateway.XmiDomParser;

/**
 * @author rouanehm
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class XmiReader extends AbstractReader {

	public XmiReader(Reader r) {
		super(r);
	}

	public void run() {
		try{
			InputSource is=new InputSource(getStream());		
			XmiDomParser parser = new XmiDomParser(is);
			XmiData xmidata =  parser.loadXMIData();
			xmidata.displayContents();	
			RcfBuilder rcfBuilder = new RcfBuilder(xmidata);
			data =  rcfBuilder.getRCF();	
		}catch(Exception e){
		e.printStackTrace();
		  if(jobObserv!=null) {
			jobObserv.sendMessage(e.getMessage());
			jobObserv.jobEnd(false);
		  }
		  return;
	  }
	  if(jobObserv!=null) jobObserv.jobEnd(true);
	}
}
