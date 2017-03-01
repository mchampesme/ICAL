/*
 *  Copyright LIPN
 *  contributor(s) : Marc Champesme (2006) marc.champesme@lipn.univ-paris13.fr
 *  
 *  This software is a computer program whose purpose is the Incremental construction of Alpha lattices.
 *  
 *  This software is governed by the CeCILL license under French law and
 *  abiding by the rules of distribution of free software.  You can  use, 
 *  modify and/ or redistribute the software under the terms of the CeCILL
 *  license as circulated by CEA, CNRS and INRIA at the following URL
 *  "http://www.cecill.info". 
 *  
 *  As a counterpart to the access to the source code and  rights to copy,
 *  modify and redistribute granted by the license, users are provided only
 *  with a limited warranty  and the software's author,  the holder of the
 *  economic rights,  and the successive licensors  have only  limited
 *  liability. 
 *  
 *  In this respect, the user's attention is drawn to the risks associated
 *  with loading,  using,  modifying and/or developing or reproducing the
 *  software by the user in light of its specific status of free software,
 *  that may mean  that it is complicated to manipulate,  and  that  also
 *  therefore means  that it is reserved for developers  and  experienced
 *  professionals having in-depth computer knowledge. Users are therefore
 *  encouraged to load and test the software's suitability as regards their
 *  requirements in conditions enabling the security of their systems and/or 
 *  data to be ensured and,  more generally, to use and operate it in the 
 *  same conditions as regards security. 
 *  
 *  The fact that you are presently reading this means that you have had
 *  knowledge of the CeCILL license and that you accept its terms.
 */
package lattice.alpha.algorithm.merge;

import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import lattice.alpha.rules.generator.Jen;
import lattice.alpha.util.BGConceptNode;
import lattice.alpha.util.BitSetExtent;
import lattice.alpha.util.CoupleOfNodes;
import lattice.alpha.util.NodeListByIntent;
import lattice.util.concept.Concept;
import lattice.util.concept.Extent;
import lattice.util.concept.Intent;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.CompleteConceptLatticeImp;
import lattice.util.structure.Node;

/**
 * @author     Naima Eljaouhari
 * @author     Marc Champesme
 * @since      mai 2005
 * @version    8 janvier 2006
 */
public class MergeAlpha {
	
	/**
	 *  Description of the Method
	 *
	 * @param  classList  Description of the Parameter
	 * @param  lat1       Description of the Parameter
	 * @param  lat2       Description of the Parameter
	 * @param  alpha      Description of the Parameter
	 * @param  gens       Description of the Parameter
	 * @return            Description of the Return Value
	 */
	public static CompleteConceptLattice fusionne(List<Extent> classList, CompleteConceptLattice lat1,
			CompleteConceptLattice lat2,
			double alpha, boolean gens) {
		MergeAlpha myMerge = new MergeAlpha(classList, lat1, lat2, alpha, gens);
		myMerge.fusionner();
		return myMerge.mergeLattice;
	}

	private List<Extent> classList;

	private CompleteConceptLattice lat1;

	private Extent objectSetLat1;

	private CompleteConceptLattice lat2;

	private Extent objectSetLat2;

	private CompleteConceptLattice mergeLattice;

	private Intent attributeSetLat;

	private Extent objectSetMergeLat;

	private Map<CoupleOfNodes<Concept>, Node<Concept>> psiMap;

	private double alphaValue;

	private boolean generatorsMustBeComputed;


	/**
	 *  Constructor for the MergeAlpha object
	 *
	 * @param  classList                 Description of the Parameter
	 * @param  l1                        Description of the Parameter
	 * @param  l2                        Description of the Parameter
	 * @param  alpha                     Description of the Parameter
	 * @param  generatorsMustBeComputed  Description of the Parameter
	 */
	/*@
	  @ requires classList != null;
	  @ requires classList.size() >= 2;
	  @ requires (\forall int i; i >= 0 && i < classList.size();
	  @                         classList.get(i) instanceof BitSetExtent);
	  @ requires l1 != null;
	  @ requires l1.getTopConceptNode() != null;
	  @ requires l1.getTopConceptNode().getParents().isEmpty();
	  @ requires !l1.getTopConceptNode().getChildren().isEmpty();
	  @ requires l1.getBottomConceptNode() != null;
	  @ requires !l1.getBottomConceptNode().getParents().isEmpty();
	  @ requires l1.getBottomConceptNode().getChildren().isEmpty();
	  @ requires l2 != null;
	  @ requires l2.getTopConceptNode() != null;
	  @ requires l2.getTopConceptNode().getParents().isEmpty();
	  @ requires !l2.getTopConceptNode().getChildren().isEmpty();
	  @ requires l2.getBottomConceptNode() != null;
	  @ requires !l2.getBottomConceptNode().getParents().isEmpty();
	  @ requires l2.getBottomConceptNode().getChildren().isEmpty();
	  @ requires alpha >= 0 && alpha <= 1;
	  @*/
	public MergeAlpha(List<Extent> classList, CompleteConceptLattice l1, CompleteConceptLattice l2,
			double alpha, boolean generatorsMustBeComputed) {
		lat1 = l1;
		lat2 = l2;
		alphaValue = alpha;
		this.generatorsMustBeComputed = generatorsMustBeComputed;
		this.classList = classList;

		// les deux treillis ont les memes attributs, qui sont aussi
		// les attributs du treillis resultat
		Node<Concept> bottomNode = lat1.getBottom();
		if (bottomNode == null) {
			System.out.println("BottomNode is null");
		}
		Concept bottomConcept = bottomNode.getContent();
		attributeSetLat = bottomConcept.getIntent();

		// l'ensemble d'objets du treillis resultat est l'union des objets des
		// deux treillis source
		objectSetLat1 = (BitSetExtent) lat1.getTop().getContent().getExtent();
		objectSetLat2 = (BitSetExtent) lat2.getTop().getContent().getExtent();

		objectSetMergeLat = objectSetLat1.extentUnion(objectSetLat2);

		// initialisation du treillis resultat
		mergeLattice = new CompleteConceptLatticeImp();
		mergeLattice.initialiseIntentLevelIndex(attributeSetLat.size() + 1);
		psiMap = new HashMap<CoupleOfNodes<Concept>,Node<Concept>>(lat1.size() * lat2.size());
	}


	/**
	 *  Description of the Method
	 *
	 * @param  extent      Description of the Parameter
	 * @param  classList   Description of the Parameter
	 * @param  alphaValue  Description of the Parameter
	 * @return             Description of the Return Value
	 */
	public static Extent alphaProjection(List<Extent> classList, double alphaValue, BitSetExtent extent) {
		BitSetExtent alphaExtent = new BitSetExtent(extent.domain());
		double countseuil = 0;
		Iterator<Extent> classIter = classList.iterator();
		while (classIter.hasNext()) {
			BitSetExtent currentClass;
			currentClass = (BitSetExtent) classIter.next();
			BitSetExtent currentRelationExtent = (BitSetExtent) extent.intersection(currentClass);
			if (currentClass.size() > 0) {
				countseuil = (double) currentRelationExtent.size()
						 / (double) currentClass.size();
				//System.out.println("countseuil=" +
				//currentRelationExtent.size() + "/" + relationObjectSet.size()
				//+ "=" + countseuil);
			}
			if (countseuil >= alphaValue) {
				alphaExtent.fastAddAll(currentRelationExtent);
			}
		}
		//System.out.println("Extent:" + extent + " --> AlphaExtent(" + alphaValue +
		//"):" + alphaExtent);
		return alphaExtent;
	}


	/**
	 * @param  child
	 * @param  parents
	 * @return
	 */
	/*@
	  @ requires child != null;
	  @ requires parents != null;
	  @*/
	public List<Node<Concept>> minClosed(Node<Concept> child, NodeListByIntent parents) {
		List<Node<Concept>> minClo = new ArrayList<Node<Concept>>();
		List<Extent> extentList = new ArrayList<Extent>();
		Extent childExtent = child.getContent().getExtent();
		Extent curExtent = childExtent;

		extentList.add(childExtent);

		Iterator<Node<Concept>> parentIter = parents.decIterator();
		while (parentIter.hasNext()) {
            Node<Concept> parent = parentIter.next();
			Extent parentExtent = parent.getContent().getExtent();

			boolean testdesortie = true;
			Iterator<Extent> extentIter = extentList.iterator();
			while (extentIter.hasNext() && testdesortie) {
				curExtent = extentIter.next();
				Extent test = alphaProjection(classList, alphaValue, (BitSetExtent) curExtent.extentIntersection(parentExtent));
				testdesortie = childExtent.equals(test);
			}

			if (testdesortie) {
				minClo.add(parent);
				extentList.add(parentExtent);
				curExtent = curExtent.extentUnion(parentExtent);
			}
		}
		return minClo;
	}


	/**
	 *  Gets the psiImage attribute of the MergeAlpha object
	 *
	 * @param  couple  Description of the Parameter
	 * @return         The psiImage value
	 */
	public Node<Concept> getPsiImage(CoupleOfNodes<Concept> couple) {
		return psiMap.get(couple);
	}


	/**
	 *  Description of the Method
	 *
	 * @param  couple     Description of the Parameter
	 * @param  imageNode  Description of the Parameter
	 */
	public void putPsiImage(CoupleOfNodes<Concept> couple, Node<Concept> imageNode) {
		psiMap.put(couple, imageNode);
	}


	/**
	 *  Description of the Method
	 *
	 * @param  imageNode  Description of the Parameter
	 * @param  psiImages  Description of the Parameter
	 */
	public void insertNode(Node<Concept> imageNode, NodeListByIntent psiImages) {

		// Calcul des parents
        for (Node<Concept> parent : minClosed(imageNode, psiImages)) {
			imageNode.linkToUpperCovers(parent);
			//mergeLattice.setUpperCover(parent, imageNode);
		}

		// Insertion dans le treillis
		mergeLattice.incNbOfNodes();
		mergeLattice.add(imageNode);

		Concept imageConcept = imageNode.getContent();
		Intent imageIntent = imageConcept.getIntent();
		Extent imageExtent = imageConcept.getExtent();
		if (imageIntent.size() == attributeSetLat.size()) {
			mergeLattice.setBottom(imageNode);
		}
		if (imageExtent.size() == objectSetMergeLat.size()) {
			mergeLattice.setTop(imageNode);
		}
	}


	/**
	 *  Description of the Method
	 */
	public void fusionner() {
		Date dateStart = new Date();
		System.out.println("Fusion start at " + dateStart);
		System.out.println("First lattice:" + lat1.size() + " nodes.");
		System.out.println("Second lattice:" + lat2.size() + " nodes.");
		// calcul des Intent du bottom

		int numberofnode = 0;
		// Parcours du premier treillis
//		int nbNode1 = 0;
//		int nbNode2 = 0;
        for (Node<Concept> n1 : lat1) {
//			nbNode1++;
			Intent n1Intent = n1.getContent().getIntent();
			Extent n1Extent = n1.getContent().getExtent();

			// Parcours du deuxième treillis
            for (Node<Concept> n2 : lat2) {
//				nbNode2++;
				//System.out.println("nbNode1=" + nbNode1 + ", nbNode2=" + nbNode2);
				Intent n2Intent = n2.getContent().getIntent();
				Extent n2Extent = n2.getContent().getExtent();
				CoupleOfNodes<Concept> couple = new CoupleOfNodes<Concept>(n1, n2);
                Node<Concept> imageNode = null;

				// calcule de intent du nouveau noeud
				Intent imageIntent = n1Intent.intentIntersection(n2Intent);

				// recupération
				// des noeud qui peuvent etre des noeud du nouveau lattice
				NodeListByIntent psiImages = new NodeListByIntent(imageIntent.size());
				Iterator<CoupleOfNodes<Concept>> iterUpperCovers = couple.upperCovers().iterator();
				while (iterUpperCovers.hasNext() && imageNode == null) {
					CoupleOfNodes<Concept> upperCover = iterUpperCovers.next();
					Node<Concept> coverImage = getPsiImage(upperCover);
					if (coverImage != null) {
						psiImages.add(coverImage);
						if (coverImage.getContent().getIntent().size() == imageIntent.size()) {
							imageNode = coverImage;
						}
					}
				}

				if (imageNode == null) {
					// Insert new node
					numberofnode++;
					Extent imageExtent = n1Extent.extentUnion(n2Extent);
					imageNode = new BGConceptNode(imageExtent, imageIntent);
					insertNode(imageNode, psiImages);
					if (numberofnode % 100 == 0) {
						System.out.println("Fusion(" + numberofnode + "): insert new node int#" + imageIntent.size()
								 + "/ext#" + imageExtent.size());
					}
					// end insert new node
				}
				putPsiImage(couple, imageNode);
			}
			// end iter second lattice
		}
		// end iter first latttice
		//System.out.println("Fusion done: bottomNode is " + mergeLattice.getBottomConceptNode());
		Date dateEnd = new Date();
		System.out.println("Fusion done at " + dateEnd + " resulting lattice has " + mergeLattice.size() + " nodes");
		long time = dateEnd.getTime() - dateStart.getTime();
		long timeSec = (long) (time / 1000);
		long timeMin = (long) (timeSec / 60);
		System.out.println("LatticeMerge: Total processing time "
				 + time + "ms or " + timeMin + "mn " + (timeSec - timeMin * 60) + "s");

		if (generatorsMustBeComputed) {
			System.out.println("Computing generators:");
			Jen algoGenerateurs = new Jen(mergeLattice);
			algoGenerateurs.computeLatticeGenerators();
			System.out.println("Generators computation done.");
		}
		//System.out.println("Fusion really done: bottomNode is " + mergeLattice.getBottomConceptNode());
	}

}

