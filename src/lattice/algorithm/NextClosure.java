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
	 * Created on 30 juin 2003
	 * 
	 * To change the template for this generated file go to
	 * Window>Preferences>Java>Code Generation>Code and Comments
	 */

package lattice.algorithm;


import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;

import java.util.*;
	
	/**
	 * @author Nelly BENET & Frédéric SCHWEDA
	 * Adapted to Galicia by Nehmé Kamal
	 * To change the template for this generated type comment go to
	 * Window>Preferences>Java>Code Generation>Code and Comments
	 * 
	 *     Cette classe implémente l'algorithme de Ganter sur des données binaires.
	 * Cet algorithme permet de retrouver la liste des concepts qui permettront
	 * de tracer le treillis par la suite. 	 
	 */
	public class NextClosure extends LatticeAlgorithm {
		
		private List<FormalAttribute> attributes;
		   
		private Hashtable concepts = new Hashtable();
		private Hashtable conceptAttribute = new Hashtable();
		
		public String str = "";
		
			/**
			* Constructor for Ganter Algo.
			* @param void
			*/
			public NextClosure() {
				super();
			}

			/**
			 * Constructor for Ganter Algo.
			 * @param MatrixBinaryRelationBuilder 
			 */
			public NextClosure(MatrixBinaryRelationBuilder bRel) {			
				super(bRel);	
			}
	
			/**
			 * @param void
			 * */
			public void doAlgorithm() {
				Date date = new Date();
				System.out.println( "Next Closure Algorithm (binary data)");
				//System.out.println("Begin Execution at: " + date.toString());
				//str = str+"Next-Closure \t Begin Execution at: " + date.toString();
				
				
				try {
					AlgoPrincipale();
					//System.out.println("Nbr of Concepts: " + getLattice().getSize());
				} catch (BadInputDataException e) {
					System.out.println("An error happened when trying to access to the binary relation...");
					e.printStackTrace();
				}
				
				
				date = new Date();
				//System.out.println("End Execution at: " + date.toString());
				//str = str +"\t End Execution at: " + date.toString()+"\t Nbr of Concepts: " + getLattice().getSize();
			
			
				
			}
		
			 /**
			 * @return String
			 */
			public String getDescription() {
				return "Next Closure Algorithm (binary data)";
			}
		
			/**
			 * @param void
			 * @return void 
			 * @throws BadInputDataException
			 * */
			private void AlgoPrincipale() throws BadInputDataException{ 
				
				int nbObj = getBinaryRelation().getObjectsNumber();
				int nbAttr = getBinaryRelation().getAttributesNumber();			
				int i,j,k;
				
				attributes = this.getBinaryRelation().getAttributes();
				
				// X Ensemble des attributs
				int[] X = new int[nbAttr];
				
				// Initialisation de X
				for (i=0;i<nbAttr;i++) X[i]=1;
				
				// A Sous-Ensemble de X
				int[] A = new int[nbAttr];
			
				// S = X - A
				int[] S = new int[nbAttr];

				// I Sous-Ensemble I = inc(A,i)
				int[] I = new int[nbAttr];

				// I_A Sous-Ensemble I_A = I-A
				int[] I_A = new int[nbAttr];
					
				// O ensemble des objets 
				int[] O = new int[nbObj];
							 		
				// attCom ensemble des attribut communs aux objets de O 
				int[] attCom = new int[nbAttr];							 		
							 						
				// Fh Ensemble des Fermés (concepts)				
				Vector Fh = new Vector();
				
				// mémoire des non fermés précédents
				// contient des SetExtent
				Vector vIntent = new Vector();			
				Vector vSetI = new Vector();																		

				SetExtent extent = new SetExtent();							
				SetIntent intent = new SetIntent();
				
				//Concept concept = new ConceptImp(extent,intent);
				
				List<FormalObject> v = getBinaryRelation().getObjects();
				
				for (int s=0; s<v.size();s++){
					FormalObject fo = (FormalObject) v.get(s);
					extent.add(fo);
				}
				
				Concept concept = new ConceptImp(extent,intent);
				
				ConceptNode nCurrent = new ConceptNodeImp((ConceptImp)concept);

				// On met le premier concept dans Fh : le concept vide
				Fh.add(concept);
				
				concepts.put(nCurrent.getContent().getExtent(),nCurrent);
				
				int testFin = 1;
				int lower;
				int elt_i=0;
											
				for (i=0;i<nbAttr;i++)
					if (X[i]!= A[i])
						testFin=0;								 					
				
				// tant que A ne contient pas tous les attributs
				while (testFin == 0)
				{												
					lower = 0;
					
					// Construction de S = X - A
					for (i=0;i<nbAttr;i++)
						if (X[i]==1 && A[i]==1)
							S[i]=0;
						else
							S[i]=X[i];
													
					while (lower == 0)
					{
						i=0;						
						int trouve=0;
						// Recherche du premier elt de S
						while (trouve==0 && i<nbAttr)
						{
							if (S[i]==1)
							{
								elt_i=i;
								trouve=1;
							}							
							i++;	
						}							
						// elt_i = premier element de S						
												
						if (trouve==1)
						{						
							// on prive S de elt_i
							S[elt_i]=0;
						
							// Initialisation de I a vide
							for (j=0;j<nbAttr;j++)
								I[j]=0;
							
							// Calcul de I = inc (A,i)
							I[elt_i]=1;
							for (j=elt_i+1;j<nbAttr;j++)
								if (A[j]==1) I[j]=1;
							
							// construction du set de I															
							// Affichage de I
							Intent setI = new SetIntent();
							//System.out.print("\nI : ");
							for (j=0;j<nbAttr;j++)							
								if (I[j]==1) 
								{
									FormalAttribute fat = getBinaryRelation().getFormalAttribute(j);
									setI.add(fat);
								} 
								
							// I* = h(I) : Calcul de la fermeture de I
														
							// on initialise le tableau des objets et celui des attribut communs
							for (j=0;j<nbObj;j++) O[j]=0;
							for (j=0;j<nbAttr;j++) attCom[j]=0;
						 
							int objOk=0;
							int premier;
							// On récupère tout les objets ayant tous les attributs de I
							for (j=0;j<nbObj;j++)
							{			
								premier=0;
								for (k=0;k<nbAttr;k++)
								{
									if (I[k]==1)
									{
										premier++;	
										
										if (getBinaryRelation().getRelation(j,k).toString().equals("X"))
										{																																	
											if (premier == 1)												
												objOk=1; 
										}
										else
										{											
											objOk=0;											
										}
									}																												
								}
						
								if (objOk==1) O[j]=1; 		
							}						
						
							// pour chacun des attributs on regarde si les objets
							// ont cet attribut en commun
							for (j=0;j<nbAttr;j++)
							{					
								premier = 0;
								int attOk = 0;
								for (k=0;k<nbObj;k++)
								{
									if (O[k]==1)
									{	
										if (getBinaryRelation().getRelation(k,j).toString().equals("X"))
										{
											premier++;
											if (premier == 1) attOk=1;																				
										}										
										else
										{
											attOk=0;
											premier++;
										}										
									}																																											
								}
								// si AttrOk c'est que l'attribut j est commun aux objets
								if (attOk==1)
									attCom[j]=1;							
							}							
						
							// construction du concept ou du non concept en cours
							SetIntent unSetIntent = new SetIntent();
							SetExtent unSetExtent = new SetExtent();							
																					
							int vide=1;
							// Construction des intensions et extensions
							for (j=0;j<nbObj;j++)
								if (O[j]==1)
								{
									 vide=0;
									 FormalObject fobj = getBinaryRelation().getFormalObject(j);
									 unSetExtent.add(fobj);
								}
								
							//s'il n'y a aucun objet sélectionné on ajoute tous les elements au non fermé 
							if (vide==1) 
								for (j=0;j<nbAttr;j++)
								{
									FormalAttribute fatt = getBinaryRelation().getFormalAttribute(j);
									unSetIntent.add(fatt);
									attCom[j]=1;									
								}																																		
							else						
								// Construction de l'intension : h(inc(A,i))															
								for (j=0;j<nbAttr;j++)
									if (attCom[j]==1){
										FormalAttribute fat = getBinaryRelation().getFormalAttribute(j);
										unSetIntent.add(fat);
									}
																							
							// On compare ensuite attCom et I 
							// Si I est égal a attCom 
							// nous avons trouvé un fermé
							int idem=1;
							int dernier=nbAttr+1;
							for (j=0;j<nbAttr;j++)								
								if (attCom[j]!=I[j])
									if (A[j]!=1)
										idem=0;
									else
									{										
										// on vérifie que tous les objets ont cet attribut en commun
										for (k=0;k<nbObj;k++)
											if (O[k]==1 && getBinaryRelation().getRelation(k,j).toString()=="0")
												idem=0; 
									}
							
							if (idem == 0)
							{
								// test avec les elements non fermés trouvés précedemment
								// pour le même ensemble A d'attributs
								// si l'union des SetI est égale a a attCom : on trouve un fermé
								int l=0, ok=0;
								Intent unSetUni = new SetIntent();
								while (l<vIntent.size() && ok==0)
								{																		
										if (l==0)
											unSetUni = setI.intentUnion((Intent)vSetI.elementAt(l));
										else
											unSetUni = unSetUni.intentUnion((Intent)vSetI.elementAt(l));
									
										
										premier=0;
										for (j=0;j<nbAttr;j++)
											if (attCom[j]==1)										
											{
												FormalAttribute fat = getBinaryRelation().getFormalAttribute(j);
												premier++;
													if (unSetUni.contains(fat)==true)
													{
														if (premier==1) ok=1;													
													}												
													else
													{
														int appartient=0;
														// si l'attributs appartient a A alors ok													
														if (A[j]==1) 
														{
															appartient=1;
															if (premier==1) ok=1;														
															// on vérifie que tous les objets ont cet attribut en commun
															for (k=0;k<nbObj;k++)
																if (O[k]==1 && getBinaryRelation().getRelation(k,j).toString()=="0")
																	ok=0; 									
														} 
														// sinon non trouvé						
														if (appartient!=1)
														{ 
															ok=0;  														
														}																										
													} 
												}
										if (ok==1)
										{
											//System.out.println(" on a trouve un fermé par l'union de deux non fermés");
											idem=1;		
											
										}																																																							
									l++;												
								}// Fin while																											 							
							}// Fin si
										
							// s'il s'agit d'un fermé									
							if (idem==1) 
							{																
								
								Intent unIntent;
								unIntent = unSetIntent;	
								Extent unExtent;
								unExtent = unSetExtent;	
								
								Concept c = new ConceptImp(unSetExtent,unSetIntent);										
								Fh.addElement(c);
								
								getLattice().incNbOfNodes();
								
								ConceptNodeImp node = new ConceptNodeImp((ConceptImp)c);
								
								concepts.put(node.getContent().getExtent(),node);
								
								Iterator itr = unSetIntent.iterator();
								while (itr.hasNext()){
									FormalAttribute fa = (FormalAttribute)itr.next();
									Intent faToIntent = new SetIntent();
									faToIntent.add(fa);
									ConceptNode attNode = (ConceptNodeImp)conceptAttribute.get(faToIntent);
									if (attNode == null)
										conceptAttribute.put(faToIntent,node);
								}
								
								
								
								// calcul de I-A = I-A
								for (j=0;j<nbAttr;j++)
									if (I[j]==1 && A[j]==1)
										I_A[j]=0;
									else
										{
											I_A[j]=I[j];
											// récupération du dernier élément de I_A
											if (I_A[j]==1)
												dernier=j;
										} 																																										
								
								if (dernier<=elt_i)
								{
									lower=1;
									// ajout du fermé a l'ensemble des fermés
									for (j=0;j<nbAttr;j++)
										A[j]=attCom[j];									
								}
								
//								 Initialisation de la mémoire des non fermés précédents
								// Vider le vector vExtent
								vIntent.clear();
								vSetI.clear();
								setI.clear();
							}
							else // si l'élément n'est pas un fermé
							{
								// on le stocke																			
								vIntent.addElement(unSetIntent);
								vSetI.addElement(setI);
								}							
							// Fin du calcul de la fermeture												
						} // Fin du si trouvé	 													
					} // fin while			
								
					// test de fin de boucle
					testFin=1;
					for (i=0;i<nbAttr;i++)
						if (X[i]!= A[i])
							testFin = 0;								
				}	
				
				
				List<FormalObject> v1 = getBinaryRelation().getObjects();
				Extent topExtent = new SetExtent();
				
				for (int s=0; s<v1.size();s++){
					FormalObject fo = (FormalObject) v.get(s);
					topExtent.add(fo);
				}
				
				ConceptNodeImp topNode = (ConceptNodeImp)concepts.get(topExtent);
				getLattice().setTop(topNode);
				
				this.NR_Gen_Hasse(concepts,conceptAttribute,attributes);
				
				//System.out.println("Nbr of Concepts: "+getLattice().getSize());
				
			}// fin fction
		
		
		
		public void NR_Gen_Hasse(Hashtable concepts, Hashtable conceptAttribute, List<FormalAttribute> attributes2){
			
			
			Hashtable Counter = new Hashtable();
			
			Iterator it = concepts.keySet().iterator();
			
			while (it.hasNext()){
			  Vector listeConceptsCandidats = new Vector();
			  ConceptNode cCourant = (ConceptNodeImp) concepts.get(it.next());
			
			  Iterator itD = calculDifference(attributes2, cCourant.getContent().getIntent()).iterator();
			  while (itD.hasNext()) {
				FormalAttribute a = (FormalAttribute) itD.next();
			
				
				Intent in = new SetIntent();
				in.add(a);
				
				Extent extConceptAtt = new SetExtent();
				Extent E = new SetExtent();
				
				ConceptNode conceptAttNode = (ConceptNodeImp)conceptAttribute.get(in);
				if (conceptAttNode !=null){
				
				extConceptAtt = ((ConceptNode)conceptAttribute.get(in)).getContent().getExtent();
			
				E = extConceptAtt.extentIntersection(cCourant.getContent().getExtent());	
				
				ConceptNode candidat = (ConceptNodeImp) concepts.get(E);
				
				  if (candidat != null){
				  	Integer cCounter = (Integer) Counter.get(candidat);
				  	if(cCounter == null)
				  		cCounter = new Integer(0);
					
				  	int cCount = cCounter.intValue();
				  	cCount++;
				  	
				  
					Counter.put(candidat,new Integer(cCount));
					
					cCount = ((Integer)Counter.get(candidat)).intValue();
					
					if (cCount == 1) 
						listeConceptsCandidats.add(candidat);
					
				
					if (cCount + cCourant.getContent().getIntent().size() == candidat.getContent().getIntent().size()) {
					  newLink(cCourant,candidat);
					 
					}
				  }
				}
			  }
			  Counter.clear();
			}
		  }

		private void newLink(ConceptNode node,ConceptNode childNode) {
		    getLattice().setUpperCover(node, childNode);
		  }
		
		private List<FormalAttribute> calculDifference(List<FormalAttribute> attributes2, Intent intent){
			
			List<FormalAttribute> v = new Vector<FormalAttribute>(attributes2);
			
			Iterator itr = intent.iterator();
			
			while (itr.hasNext()){
				FormalAttribute fa = (FormalAttribute)itr.next();
				v.remove(fa);
			}
			
			
			return v;
		}
		
		public String getResults(){
			return str;
		}
		
} // Fin de la Classe de l'algorithme de Ganter pour des données binaires

