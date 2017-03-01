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

package lattice.gsh.algorithm;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Vector;

import lattice.algorithm.LatticeAlgorithm;
import lattice.gui.RelationalContextEditor;
import lattice.util.concept.Concept;
import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalAttributeValue;
import lattice.util.concept.FormalObject;
import lattice.util.concept.InterObjectBinaryRelationAttribute;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.LatticeGraph;
import lattice.util.structure.Node;

/**
 * @author roume
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class Gagci_NoInc extends LatticeAlgorithm {

	private RelationalContextEditor editor=null;
	// Devrai a terme disparaitre ... Un jour ...
	// Sert a visualiser les matrice completer dans l'editor mais cela pourrai etre fait via evennement 

	private Vector setOfEnrichingRelations=null;
	//size==i : the Ki
	private Vector SetOfRelationalAttributes=null; 
	// size == i : the Rel(Ki)
	// An element of this vector is a Hashtable for Rel(Ki) 
	// In this hashtable a Kj name is associate to a set (Vector) of inter-object relation : Ki -> kj
	
	private Hashtable setOfSHG=null;
	// Des graphs initiaux pour les Ki : (Ki_name,Ki_LatticeGraph)
	// Dans ces graphs les intensions ne sont pas utile, 
	// seule les extension comporte des infos utils afin de pouvoir executer 'complete(...)'
	
	/**
	 * Constructor for Gagci_NoInc.
	 */
	public Gagci_NoInc() {
		super();
	}

	/**
	 * Constructor for Gagci_NoInc.
	 * @param bRel
	 */
	public Gagci_NoInc(MatrixBinaryRelationBuilder bRel) {
		super(bRel);
	}

	/**
	 * Constructor for Gagci_NoInc.
	 * @param bRel
	 */
	public Gagci_NoInc(MatrixBinaryRelationBuilder bRel, Vector setOfEnrichingRelations, Vector SetOfRelationalAttributes, Hashtable setOfInitGraph, RelationalContextEditor editor) {
		super(bRel);
		this.setOfEnrichingRelations=setOfEnrichingRelations; 
		this.SetOfRelationalAttributes=SetOfRelationalAttributes;  
		this.setOfSHG=setOfInitGraph;
		this.editor=editor;
	}

	/**
	 * @see lattice.algorithm.LatticeAlgorithm#doAlgorithm()
	 */
	public void doAlgorithm() {
		doGagciNoInc();
	}

	/**
	 * The none incremental GAGCI algorithm 
	 * binRel, setOfRelations and SetOfRelationalAttributes should be filled
	 */
	public void doGagciNoInc() {
		// Cette algo a été developpé dans la phylosophie du papier FCAKDD'02 (Huchard,Roume,Valtchev)
		boolean fixPoint=false;
		boolean shgModif;
		int nbIter=1;
		while(!fixPoint){

			sendJobPercentage(0);

			MatrixBinaryRelationBuilder Ki=null; //One Binary Relation
			InterObjectBinaryRelation aRelj_Ki=null; //One InterObjectRelation : Ki -> Kj		
			Vector theRelj_Ki=null; // The Rel(Ki) with Kj
			shgModif=false;
			for(int i=0;i<setOfEnrichingRelations.size();i++){
				Ki=(MatrixBinaryRelationBuilder)((MatrixBinaryRelationBuilder)setOfEnrichingRelations.elementAt(i)).clone();
				// Just A Mess
				if(jobObserv!=null) jobObserv.sendMessage(Ki.getName()+" is Considered\n");
				for(Enumeration iter=((Hashtable)SetOfRelationalAttributes.elementAt(i)).keys();iter.hasMoreElements();){
					String theKj_Name=iter.nextElement().toString();
					theRelj_Ki=(Vector)((Hashtable)SetOfRelationalAttributes.elementAt(i)).get(theKj_Name);
					for(int j=0;j<theRelj_Ki.size();j++){
						aRelj_Ki=(InterObjectBinaryRelation)theRelj_Ki.elementAt(j);
						complete(Ki,aRelj_Ki,(LatticeGraph)setOfSHG.get(theKj_Name));
					}
					// Just A Mess
					if(jobObserv!=null) jobObserv.sendMessage(Ki.getName()+"=>"+theKj_Name+" Relational Attributes is Completed\n");
				}
				CERES anAlgo=new CERES(Ki);
				anAlgo.doAlgorithm();
				Ki.setLattice(anAlgo.getLattice());
				
				// Just A Mess
				if(jobObserv!=null) jobObserv.sendMessage(Ki.getName()+" CERES is done\n");
				if(setOfSHG.get(Ki.getName())==null) {
					shgModif=true;
					setOfSHG.put(Ki.getName(),anAlgo.getLattice());
				} else {
					shgModif=isModified((LatticeGraph)setOfSHG.get(Ki.getName()),(LatticeGraph)anAlgo.getLattice());
					setOfSHG.put(Ki.getName(),anAlgo.getLattice());
				}
				
				Ki.setName(Ki.getName()+"_"+nbIter);
				Ki.getLattice().setDescription(Ki.getName());
				if(editor!=null) {
					// Pour visualiser les contextes intermediaire
					editor.addBinaryRelation(Ki);
					editor.showAssociatedGraph();
				} 
				sendJobPercentage(((i+1)*100)/setOfEnrichingRelations.size());
			}
			if(!shgModif) fixPoint=true;

			// Just A Mess
			if(jobObserv!=null) jobObserv.sendMessage("Gagci_NoInc Num iteration = "+nbIter+"\n");
			nbIter++;
			
		}
		
		// Positionnement des graph resultat
		setLattice((LatticeGraph)setOfSHG.get(getBinaryRelation().getName()));
		getBinaryRelation().setLattice((LatticeGraph)setOfSHG.get(getBinaryRelation().getName()));
		for(int i=0;i<setOfEnrichingRelations.size();i++){
			((MatrixBinaryRelationBuilder)setOfEnrichingRelations.elementAt(i)).setLattice((LatticeGraph)setOfSHG.get(((MatrixBinaryRelationBuilder)setOfEnrichingRelations.elementAt(i)).getName()));
		}
	}

	private boolean isModified(LatticeGraph firstG, LatticeGraph secondG){
		if(firstG.getAllNodes().size()==secondG.getAllNodes().size()){
			if(!isModifiedRec(firstG.getTop(),secondG.getTop())) return false;
		}
		return true;
	}
	private boolean isModifiedRec(Node<Concept> firstN, Node<Concept> secondN){
		// Ceci devrai fonctionner car les Ki sont complété toujours de la même manière 
		// et donc les SHG devrais être avoir un ordonnancement de construction identique
		// La seule difference que l'on doit trouver est sur le nom des attributs formel " =Node_X "
		boolean res=true;
		if(firstN.getContent().getIntent().size()==secondN.getContent().getIntent().size()) {
			res=false;	
			if(firstN.getChildren().size()==secondN.getChildren().size()){
				Iterator it=firstN.getChildren().iterator();
				Iterator it2=secondN.getChildren().iterator();
				Node<Concept> N1;
				Node<Concept> N2;
				while(it.hasNext()){
					N1=(Node<Concept>)it.next();
					N2=(Node<Concept>)it2.next();
					res = res || isModifiedRec(N1,N2);
				}
			}
		}
		return res;
	}
	
	private void complete(MatrixBinaryRelationBuilder Ki,InterObjectBinaryRelation Relj_Ki,LatticeGraph aShg){
		FormalAttribute fa;
		FormalObject foKi;
		FormalObject foa;
		for(int i=0;i<Ki.getFormalObjects().length;i++){
			foKi=Ki.getFormalObjects()[i];
			for(Iterator it=Relj_Ki.getIntent(Ki.getFormalObjects()[i]).iterator();it.hasNext();){
				 //Attention si dans une improbale coincidence il y aurai deja un attribut de meme nom sa risque de planter ...
				 //Un check ici serai tres difficile a realiser ! d'un point de vue IHM 
				 foa=((InterObjectBinaryRelationAttribute)it.next()).getObject();
				 
			 	// --- Fait en sessous
			 	// Il faut eviter de melager des infos 'Objets Formel Init' et 'Node'
			 	// C'est soit tout l'un (quand shg==null) soit tout l'autre 'quand shg!=null'
			 	// ---
			 	//fa=new DefaultFormalAttribute(Relj_Ki.getRelationName()+"="+foa.toString());
			 	//if(!Ki.containsFormalAttribute(fa)) Ki.addAttribute(fa);
			 	//Ki.setRelation(Ki.indexOfFormalObject(foKi),Ki.indexOfFormalAttribute(fa),true);
			 	// --- Fait en sessous
			 
			 	if(aShg!=null){
					for(Iterator it2=aShg.getAllNodes().iterator();it2.hasNext();){
					 	Node<Concept> N=(Node<Concept>)it2.next();
					 	if(N.getContent().getExtent().contains(foa) 
							&& !(aShg.getTop()==N 
							&& N.getContent().getExtent().size()==0 
							&& N.getContent().getIntent().size()==0 )){
							// les Relj_Ki doivent être fait de tel sorte a prendre en compte la hierarchie initiale
							fa=new DefaultFormalAttribute(Relj_Ki.getName()+"=Node_"+N.getId());
							if(!Ki.contains(fa)) Ki.addAttribute(fa);
							try {
                                Ki.setRelation(foKi,fa,FormalAttributeValue.TRUE);
                            } catch (BadInputDataException e) {
                                e.printStackTrace();
                                throw new IndexOutOfBoundsException(e.getMessage());
                            }
					 	 }
				 	}
			 	} else {
					// Si pas de shg alors completion avec les infos base
					fa=new DefaultFormalAttribute(Relj_Ki.getName()+"="+foa.toString());
					if(!Ki.contains(fa)) Ki.addAttribute(fa);
					try {
                        Ki.setRelation(foKi,fa,FormalAttributeValue.TRUE);
                    } catch (BadInputDataException e) {
                        e.printStackTrace();
                        throw new IndexOutOfBoundsException(e.getMessage());
                    }
			 	}
			}
		}
	}

	/**
	 * @see lattice.util.JobObservable#getDescription()
	 */
	public String getDescription() {
		return "GAGCI - no incremental MultiFCA using GSH";
	}

	/**
	 * Returns the setOfEnrichingRelations.
	 * @return Vector
	 */
	public Vector getSetOfEnrichingRelations() {
		return setOfEnrichingRelations;
	}

	/**
	 * Returns the setOfRelationalAttributes.
	 * @return Vector
	 */
	public Vector getSetOfRelationalAttributes() {
		return SetOfRelationalAttributes;
	}

	/**
	 * Sets the setOfEnrichingRelations.
	 * @param setOfEnrichingRelations The setOfEnrichingRelations to set
	 */
	public void setSetOfEnrichingRelations(Vector setOfEnrichingRelations) {
		this.setOfEnrichingRelations = setOfEnrichingRelations;
	}

	/**
	 * Sets the setOfRelationalAttributes.
	 * @param setOfRelationalAttributes The setOfRelationalAttributes to set
	 */
	public void setSetOfRelationalAttributes(Vector setOfRelationalAttributes) {
		SetOfRelationalAttributes = setOfRelationalAttributes;
	}

}
