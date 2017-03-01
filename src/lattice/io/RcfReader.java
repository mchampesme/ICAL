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
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.StringTokenizer;
import java.util.Vector;

import javax.naming.NamingException;

import lattice.alpha.util.AlphaContext;
import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.DefaultFormalObject;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalAttributeValue;
import lattice.util.concept.FormalObject;
import lattice.util.concept.InterObjectBinaryRelationAttribute;
import lattice.util.concept.ScalingFormalAttribute;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.relation.ScalingBinaryRelation;

/** 
 * @author Mr ROUME
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class RcfReader extends AbstractReader  implements RelationalContextReader {

	/**
	 * Constructor for BasicReader.
	 * @param fileName
	 */
	public RcfReader(Reader r) {
		super(r);
	}


  /**
   * Déclaration abstraite de la méthode de lecture
   * @return Vector - les elements du treillis
   */
  public RelationalContextFamily readRelationalContext() throws NamingException,BadInputDataException,ReadingFormatException,IOException {
  	RelationalContextFamily relCtx = new RelationalContextFamily();
	String line;
	while((line=getStream().readLine())!= null && !line.equals("[END Relational Context]")) {
			if(line.equals("[Relational Context]")){
				relCtx.setName(getStream().readLine());
			}
            if(line.equals("[Binary Relation]")){
                relCtx.add(readBinaryRelation());
            }
            if(line.equals("[Binary Alpha Relation]")){
                relCtx.add(readBinaryRelation());
            }
            if(line.equals("[C/NET Context]")){
                readCNETRelationalContext(relCtx);
            }
			if(line.equals("[Inter Object Binary Relation]")){
				relCtx.add(readInterObjectBinaryRelation());
			}
			if(line.equals("[Scaling Binary Relation]")){
				relCtx.add(readScalingBinaryRelation());
			}
	}

   	return relCtx;	
  }

  public void readCNETRelationalContext(RelationalContextFamily relCtx) throws BadInputDataException,IOException {
    AlphaContext alphaCtxt = new AlphaContext("CNET data", 2300, 300, 70);
    StringTokenizer sk;
    String line = getStream().readLine();
    sk = new StringTokenizer(line.trim(),"|");
    while (line != null && !line.equals("[END]") && sk.countTokens() >= 3) {
        String objName = sk.nextToken();
        String relName = sk.nextToken();
        String attrName = sk.nextToken();
        alphaCtxt.addTriplet(objName, relName, attrName);
        
        line = getStream().readLine();
        sk = new StringTokenizer(line.trim(),"|");
    }
    Iterator classIter = alphaCtxt.getClasses().iterator();
    while (classIter.hasNext()) {
        FormalAttribute classAttr = (FormalAttribute) classIter.next();
        relCtx.add(alphaCtxt.classToMatrixBinaryRelation(classAttr));
    }
  }
  
  public MatrixBinaryRelationBuilder readBinaryRelation()
                                                           throws BadInputDataException,
                                                           IOException {
        MatrixBinaryRelationBuilder binRel = null;
        String nomRel = getStream().readLine();
        StringTokenizer sk = null;
        sk = new StringTokenizer(getStream().readLine().trim(), "|");
        List<FormalObject> lesObjs = new ArrayList<FormalObject>();
        while (sk.hasMoreElements()) {
            lesObjs.add(new DefaultFormalObject(sk.nextElement().toString()
                    .trim()));
        }
        sk = new StringTokenizer(getStream().readLine().trim(), "|");
        List<FormalAttribute> lesAtts = new ArrayList<FormalAttribute>();
        while (sk.hasMoreElements()) {
            lesAtts.add(new DefaultFormalAttribute(sk.nextElement().toString()
                    .trim()));
        }
        binRel = new MatrixBinaryRelationBuilder(nomRel, lesObjs, lesAtts);

        for (int i = 0; i < lesObjs.size(); i++) {
            sk = new StringTokenizer(getStream().readLine().trim(), " ");
            if (sk == null || sk.countTokens() < lesAtts.size()) {
                throw new BadInputDataException(
                                                "Some relationship is missing in the RCF file ("
                                                        + nomRel
                                                        + ":<MatrixBinaryRelationBuilder>)\n");
            }
            int j = 0;
            while (sk.hasMoreElements()) {
                binRel.setRelation(i, j, sk.nextToken().trim().equals("1"));
                j++;
            }
        }
        return binRel;
    } 

  public InterObjectBinaryRelation readInterObjectBinaryRelation() throws BadInputDataException,IOException {
  	InterObjectBinaryRelation ioBinRel=null;
  	String nomRel=getStream().readLine();
  	// Added by Amine.
	String sourceCtxName=getStream().readLine();
	String targetCtxName=getStream().readLine();
	// end Amine modifs
	
  	StringTokenizer sk=null;
  	sk=new StringTokenizer(getStream().readLine().trim(),"|");
  	Vector lesObjs=new Vector();
  	while(sk.hasMoreElements()){
  		lesObjs.add(new DefaultFormalObject(sk.nextElement().toString().trim())); 
  	}
  	sk=new StringTokenizer(getStream().readLine().trim(),"|");
  	Vector lesAtts=new Vector();
  	while(sk.hasMoreElements()){
  		lesAtts.add(new InterObjectBinaryRelationAttribute(new DefaultFormalObject(sk.nextElement().toString().trim()))); 
  	}
  	ioBinRel=new InterObjectBinaryRelation(lesObjs.size(),lesAtts.size());
	ioBinRel.setName(nomRel);
	ioBinRel.setObjectsContextName(sourceCtxName);
	ioBinRel.setAttributesContextName(targetCtxName);
  	
	for(int i=0;i<lesObjs.size();i++) {
		ioBinRel.replaceObject(i,(FormalObject)lesObjs.elementAt(i));
	}
	for(int j=0;j<lesAtts.size();j++) {
		ioBinRel.replaceAttribute(j,(FormalAttribute)lesAtts.elementAt(j));
	}
	
	for(int i=0;i<lesObjs.size();i++) {
		sk=new StringTokenizer(getStream().readLine().trim()," ");
		if(sk==null || sk.countTokens()<lesAtts.size()) 
		{ throw new BadInputDataException("Some relationship is missing in the RCF file ("+nomRel+":<InterObjectBinaryRelation>)\n"); }
		int j=0;
		while(sk.hasMoreElements()) {
			ioBinRel.setRelation(i,j,sk.nextToken().trim().equals("1"));
			j++;
		}
	}

  	return ioBinRel;
  } 

  public ScalingBinaryRelation readScalingBinaryRelation() throws BadInputDataException,IOException {
  	ScalingBinaryRelation scBinRel=null;
  	String nomRel=getStream().readLine();
  	StringTokenizer sk=null;
  	sk=new StringTokenizer(getStream().readLine().trim(),"|");
  	Vector lesObjs=new Vector();
  	while(sk.hasMoreElements()){
  		lesObjs.add(new DefaultFormalObject(sk.nextElement().toString().trim())); 
  	}
  	sk=new StringTokenizer(getStream().readLine().trim(),"|");
  	Vector lesAtts=new Vector();
  	StringTokenizer st2;
  	while(sk.hasMoreElements()){
  		st2=new StringTokenizer(sk.nextElement().toString(),"=");
        String strAttName = st2.nextElement().toString().trim();
  		FormalAttribute fa=new DefaultFormalAttribute(strAttName);
        String strAttValue = st2.nextElement().toString().trim();
  		FormalAttributeValue fav;
        if (strAttValue.equals("0")) {
            fav = FormalAttributeValue.FALSE;
        } else if (strAttValue.equals("X")) {
            fav = FormalAttributeValue.TRUE;
        } else {
            fav = new FormalAttributeValue(strAttValue);
        }
  		lesAtts.add(new ScalingFormalAttribute(fa,fav)); 
  	}
  	scBinRel=new ScalingBinaryRelation(lesObjs.size(),lesAtts.size());
	scBinRel.setName(nomRel);
  	
	for(int i=0;i<lesObjs.size();i++) {
		scBinRel.replaceObject(i,(FormalObject)lesObjs.elementAt(i));
	}
	for(int j=0;j<lesAtts.size();j++) {
		scBinRel.replaceAttribute(j,(FormalAttribute)lesAtts.elementAt(j));
	}
	
	for(int i=0;i<lesObjs.size();i++) {
		sk=new StringTokenizer(getStream().readLine().trim()," ");
		if(sk==null || sk.countTokens()<lesAtts.size()) 
		{ throw new BadInputDataException("Some relationship is missing in the RCF file ("+nomRel+":<ScallingBinaryRelation>)\n"); }
		int j=0;
		while(sk.hasMoreElements()) {
			scBinRel.setRelation(i,j,sk.nextToken().trim().equals("1"));
			j++;
		}
	}
  	
  	return scBinRel;
  } 

  /* (non-Javadoc)
   * @see java.lang.Runnable#run()
   */
  public void run() {
	  try{
		  data=readRelationalContext();
	  }catch(Exception e){
		  if(jobObserv!=null) {
			jobObserv.sendMessage(e.getMessage());
			jobObserv.jobEnd(false);
		  }
          System.out.println("Exception during Reading Task" + e);
		  return;
	  }
      System.out.println("Reading Task done, result:" + data);
	  if(jobObserv!=null) jobObserv.jobEnd(true);
  }
}
