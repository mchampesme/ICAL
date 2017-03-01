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
import java.util.Vector;

import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;

/**
 *
 * <p>Titre : Lattice</p>
 * <p>Description : Lecture du format IBM - treillis construit</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : Université de Montréal</p>
 * @author Alexandre Frantz et Pascal Camarda
 * @version 1.0
 */
public class IbmReader extends AbstractReader implements BinaryRelationReader
{
	MatrixBinaryRelationBuilder binRel;

  /**
   * Constructeur de la classe
   * @param r le flux de lecture
   */
  public IbmReader(Reader r)
  {
    super(r); 
  }

   public MatrixBinaryRelationBuilder readBinaryRelation() throws BadInputDataException, ReadingFormatException, IOException {
  	int nbO=0;
  	int nbA=0;
  	Vector lesRels=new Vector();
  	Vector uneRelObj;
  	StringTokenizer st=null;
  	String ligne=null;
  	int numTok=0;
  	Integer numAtt=null;
  	int nbAttLigne=0;
  	while((ligne=getStream().readLine())!=null){
  		if(!ligne.equals("") && !ligne.equals("\n")){
			st=new StringTokenizer(ligne);
			numTok=0;
			uneRelObj=new Vector();
			lesRels.add(uneRelObj);
			nbO++;
			while(st.hasMoreElements()){
				if(numTok == 0){
					nbAttLigne=Integer.parseInt(st.nextElement().toString());
				} else{
					numAtt=new Integer(st.nextElement().toString());
					uneRelObj.add(numAtt);
					if(numAtt.intValue()>nbA) nbA=numAtt.intValue();
				}
				numTok++; 			
			}
			//if(numTok!=nbAttLigne+1) throw new ReadingFormatException("Missing an Attibute on Object # : "+nbO);
  		}
  	}
	
	sendJobPercentage(50);
	
	System.out.println("nbO="+nbO);
	System.out.println("nbA="+nbA);
	binRel=new MatrixBinaryRelationBuilder(nbO,nbA);
	for(int i=0;i<nbO;i++){
		uneRelObj=(Vector)lesRels.elementAt(i);
		for(int j=0;j<uneRelObj.size();j++){
			binRel.setRelation(i,((Integer)uneRelObj.elementAt(j)).intValue()-1,true);
		}

		sendJobPercentage(50+((i*100)/(2*nbO)));

	}

	sendJobPercentage(100);

  	return binRel;
  }

	public String getDescription(){
		return "IBM Binary Relation Reader"; 
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