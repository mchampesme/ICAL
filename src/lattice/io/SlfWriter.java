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

package lattice.io;

import java.io.IOException;
import java.io.Writer;

import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.relation.MatrixBinaryRelationBuilder;

/**
 *
 * <p>Titre : Lattice</p>
 * <p>Description : Enregistrement au format Contexte</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Soci�t� : Universit� de Montr�al</p>
 * @author Alexandre Frantz et Pascal Camarda
 * @version 1.0
 */
public class SlfWriter extends AbstractWriter implements BinaryRelationWriter
{

  /**
   * Constructeur de la classe
   * @param w le flux en ecriture
   */
  public SlfWriter(Writer w)
  {
    super(w);
  }

  /**
   * Enregistre une MatrixBinaryRelationBuilder dans le flux
   * @param lattice le treillis a enregistrer
   */
  public void writeBinaryRelation (MatrixBinaryRelationBuilder binRel) throws IOException {
  	
  	getStream().write("[Lattice]\n");
  	getStream().write(""+binRel.getObjectsNumber()+"\n");
  	getStream().write(""+binRel.getAttributesNumber()+"\n");
  	getStream().write("[Objects]\n");
  	FormalObject[] lesObjs=binRel.getFormalObjects();
  	for(int i=0;i<lesObjs.length;i++){
  		getStream().write(lesObjs[i].toString()+"\n");
  	}
  	FormalAttribute[] lesAtts=binRel.getFormalAttributes();
  	getStream().write("[Attributes]\n");
  	for(int i=0;i<lesAtts.length;i++){
  		getStream().write(lesAtts[i].toString()+"\n");
  	}
	getStream().write("[relation]\n");  	
  	String ligne;
  	for(int i=0;i<lesObjs.length;i++){
  		ligne="";
  		for(int j=0;j<lesAtts.length;j++){
  			if(binRel.getRelation(lesObjs[i],lesAtts[j]).isFalse()){
  				ligne=ligne+"0 ";
  			} else {
  				ligne=ligne+"1 ";
  			}
  		}
  		getStream().write(ligne+"\n");
  		
		sendJobPercentage((i*100)/lesObjs.length);
  	}
  	
	getStream().flush();
  	getStream().close();
  	
	sendJobPercentage(100);
  	
  }
  
  public void run() {
	  try{
		  writeBinaryRelation((MatrixBinaryRelationBuilder)data);
	  }catch(Exception e){
		  if(jobObserv!=null) {
			jobObserv.sendMessage(e.getMessage());
			jobObserv.jobEnd(false);
		  }
		  return;
	  }
	  if(jobObserv!=null) jobObserv.jobEnd(true);
  }
  
}