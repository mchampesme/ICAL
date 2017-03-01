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
import java.io.Reader;
import java.util.StringTokenizer;

import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.DefaultFormalObject;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalAttributeValue;
import lattice.util.concept.FormalObject;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;

/**
 *
 * <p>Titre : Lattice</p>
 * <p>Description : Lecture du format Contexte - données brutes</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : Université de Montréal</p>
 * @author Alexandre Frantz et Pascal Camarda
 * @version 1.0
 */
public class SlfReader extends AbstractReader implements BinaryRelationReader
{
  /**
   * Constructeur
   * @param fileName le nom du fichier
   */
  public SlfReader(Reader r)
  {
    super(r);
  }

  public MatrixBinaryRelationBuilder readBinaryRelation() throws BadInputDataException, ReadingFormatException, IOException {
  	
  	
  	MatrixBinaryRelationBuilder binRel=null;
  	int nbObj=0;
  	int nbAtt=0;
  	String rel="";
  	
  	// La Ligne 1 doit contenir [Lattice]
  	if(!getStream().readLine().trim().equals("[Lattice]")) throw new ReadingFormatException("There is no [Lattice] keyword at the begining of an SLF file\n");

  	// La Ligne 2 doit contenir un Entier	
	try {
  		nbObj=Integer.parseInt(getStream().readLine().trim());
	} 
	catch (NumberFormatException nfe) 
	{ throw new ReadingFormatException("Uncomplete SLF file : Objects Number is Missing!\n"); }
  	
  	// La Ligne 3 doit contenir un Entier	
	try {
  		nbAtt=Integer.parseInt(getStream().readLine().trim());
	} 
	catch (NumberFormatException nfe) 
	{ throw new ReadingFormatException("Uncomplete SLF file : Attributes Number is Missing!\n"); }
  	

  	// Construction d'une nouvelle Relation Binaire	
	binRel=new MatrixBinaryRelationBuilder(nbObj,nbAtt);

  	// La Ligne 4 doit contenir un [Objects]	
  	if(!getStream().readLine().trim().equals("[Objects]")) throw new ReadingFormatException("The file SLF does not contain [Objects] clause\n");

	// les nbObj lignes suivantes doivent contenir des nom d'Objets
	String nomObj=null;
	for(int i=0;i<nbObj;i++) {
		nomObj=getStream().readLine().trim(); 
		if(nomObj==null || nomObj.equals("[Attributes]")) 
		{ throw new ReadingFormatException("Uncomplete SLF file : Object Name is Missing!\n"); }
		binRel.replaceObject(binRel.getFormalObjects()[i],new DefaultFormalObject(nomObj));
	}
	  	
  	// La Ligne apres les nom Objets doit contenir un [Attributes]	
  	if(!getStream().readLine().trim().equals("[Attributes]")) throw new ReadingFormatException("The file SLF does not contain [Attributes] clause\n");

	// les nbObj lignes suivantes doivent contenir des nom d'Objets
	String nomAtt=null;
	for(int i=0;i<nbAtt;i++) {
		nomAtt=getStream().readLine().trim();
		if(nomAtt==null || nomAtt.equals("[relation]")) 
		{ throw new ReadingFormatException("Uncomplete SLF file : Attribute Name is Missing!\n"); }
		binRel.replaceAttribute(binRel.getFormalAttributes()[i],new DefaultFormalAttribute(nomAtt));
	}
	 
  	// La après les nom d'attributs doit contenir un [Objects]	
  	if(!getStream().readLine().trim().equals("[relation]")) throw new ReadingFormatException("The file SLF does not contain [relation] clause\n");

	// les nbObj lignes suivantes doivent contenir des nom d'Objets
	StringTokenizer ligneRel=null;
	for(int i=0;i<nbObj;i++) {
		ligneRel=new StringTokenizer(getStream().readLine().trim()," ");
		if(ligneRel==null || ligneRel.countTokens()<nbAtt) 
		{ throw new ReadingFormatException("Uncomplete SLF file : Binary relations are Missing!\n"); }
		int j=0;
		while(ligneRel.hasMoreElements()) {
			rel=ligneRel.nextToken();
            FormalAttributeValue attValue = FormalAttributeValue.FALSE;
			if(rel.equals("1")) attValue = FormalAttributeValue.TRUE;
			FormalObject obj=binRel.getFormalObjects()[i];
			FormalAttribute att=binRel.getFormalAttributes()[j];				
			binRel.setRelation(obj,att,attValue);
			j++;
		}
		
		sendJobPercentage((i*100)/nbObj);
	}
	  	
	sendJobPercentage(100); 	
	  	
  	return binRel;
  }
  
  public String getDescription(){
  	return "SLF Binary Relation Reader"; 
  }
  
  /* (non-Javadoc)
   * @see java.lang.Runnable#run()
   */
  public void run() {
	  try{
		  data=readBinaryRelation();
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