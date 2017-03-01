/*
 * **********************************************************************
 * Copyright (C) 2004 The Galicia Team Modifications to the initial code base
 * are copyright of their respective authors, or their employers as appropriate.
 * Authorship of the modifications may be determined from the ChangeLog placed
 * at the end of this file. This program is free software; you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of the
 * License, or (at your option) any later version. This program is distributed
 * in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even
 * the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details. You should have
 * received a copy of the GNU Lesser General Public License along with this
 * program; if not, write to the Free Software Foundation, Inc., 59 Temple
 * Place, Suite 330, Boston, MA 02111-1307 USA; or visit the following url:
 * http://www.gnu.org/copyleft/lesser.html
 * **********************************************************************
 */
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

package lattice.alpha.rules.generator;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import lattice.alpha.util.BGIntent;
import lattice.alpha.util.BitSetIntent;
import lattice.gui.tooltask.AbstractJob;
import lattice.util.concept.Concept;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.Node;

/**
 * Cette classe permet de construre l'ensemble des générateurs associés aux 
 * noeuds d'un treillis.
 * 
 * @author leflocha (pour la version originale)
 * @author Marc Champesme 
 */

public class Jen extends AbstractJob {
    /**
     * nombre total de générateurs (pour l'ensemble du treillis)
     */
    private int nombreGenerateurs; 

    /**
     * Le treillis dont on cherche les générateurs
     */
    private CompleteConceptLattice myLattice;


    /**
     * @param lattice
     */
    /*@
      @ requires lattice != null;
      @ ensures getLattice() == lattice;
      @*/
    public Jen(CompleteConceptLattice lattice) {
        this.myLattice = lattice;
    }

    /** 
     * Renvoie une liste d'Intent singleton constituée à partir de
     * tous les attributs de l'Intent spécifié 
     * 
     * @param itemset
     * @return
     */
    /*@
      @ requires itemset != null;
      @ ensures \result != null;
      @ ensures \result.size() == itemset.size();
      @ ensures (\forall int i; i >= 0 && i < itemset.size();
      @                             \result.get(i) instanceof Intent
      @                             && ((Intent) \result.get(i)).size() == 1
      @                             && itemset.containsAll(((Intent) \result.get(i))));
      @ pure
      @*/
    public List<Intent> getSingletonList(Intent itemset) {
        Set<FormalAttribute> domain = null;
        if (itemset instanceof BitSetIntent) {
            domain = ((BitSetIntent) itemset).domain();
        }
        List<Intent> resultat = new ArrayList<Intent>(itemset.size());
        for (FormalAttribute att : itemset) {
            Intent singleton = null;
            if (domain == null) {
                singleton = new BGIntent();
            } else {
                singleton = new BitSetIntent(domain);
            }
            singleton.add(att);
            resultat.add(singleton);
        }
        return resultat;
    }


    /**
     * Calcul et renvoie les faces du noeud spécifié. Une face 
     * est la différence ensembliste de l'intention du noeud
     * spécifié avec l'intention de l'un de ses parents.
     * 
     * @param node Un noeud du treillis 
     * @return Les faces du noeud spécifié
     */
    /*@
      @ old Set nodeParents = node.getParents();
      @ old Intent nodeIntent = node.getConcept().getIntent();
      @ requires node != null;
      @ requires node.getConcept() != null;
      @ requires node.getParents() != null;
      @ requires node.getConcept().getIntent() != null;
      @ ensures \result != null;
      @ ensures \result.size() == nodeParents.size();
      @ ensures (\forall int i; i >= 0 && i < nodeParents.size();
      @                     \result.get(i) instanceof Intent
      @                     && nodeIntent.containsAll(((Intent) \result.get(i))));
      @ pure
      @*/
    public LinkedList<Intent> computeFacesOfNode(Node<Concept> node) {
        LinkedList<Intent> facesList = new LinkedList<Intent>();
        Intent nodeIntent = node.getContent().getIntent();
        for (Node<Concept> parentCourant : node.getParents()) {
            Intent intentDiff = nodeIntent.clone();
            intentDiff.removeAll(parentCourant.getContent().getIntent());
            facesList.add(intentDiff);
        }
        return facesList;
    }



    /**
     * Calcul les générateurs d'un noeud
     * 
     * @param faceCourante
     * @param ensembleGenerateur
     * @return
     */
    /*@
      @ requires faceCourante != null;
      @ requires ensembleGenerateur != null;
      @ requires (\forall int i; i >= 0 && i < ensembleGenerateur.size();
      @                             ensembleGenerateur.get(i) instanceof Intent);
       @ 
      @*/
    public List<Intent> modificationGenerateurs(Intent faceCourante,
                                          List<Intent> ensembleGenerateur) {
        List<Intent> resultatBloqueurMinimaux = new ArrayList<Intent>();
        List<Intent> resultatBloqueur = new ArrayList<Intent>();

        // Parcours de l'ensemble des générateurs
        for (Intent generateurCourant : ensembleGenerateur) {
            // Intersection entre la face courante et le générateur courant
            Intent intersection = generateurCourant.intentIntersection(faceCourante);
            if (intersection.isEmpty()) {
                List<Intent> nouvelEnsembleGenerateur = computeNewLockers(generateurCourant, faceCourante);
                resultatBloqueur.addAll(nouvelEnsembleGenerateur);
            } else {
                resultatBloqueurMinimaux.add(generateurCourant);
            }
        }
        if (resultatBloqueur.isEmpty()) {
            return resultatBloqueurMinimaux;
        } else {
            if (resultatBloqueurMinimaux.isEmpty()) {
                return resultatBloqueur;
            } else {
                List<Intent> resultat;
                resultat = selectLockedBlocker(resultatBloqueur,
                                       resultatBloqueurMinimaux);
                resultatBloqueur.removeAll(resultat);
                resultatBloqueurMinimaux.addAll(resultatBloqueur);
                return resultatBloqueurMinimaux;
            }
        }
    }

    /**
     * Effectue l'union du générateur courant avec chacun des attributs du
     * générateur courant.
     * 
     * @param generateurCourant
     * @param faceCourante
     * 
     * @return
     */
    /*@
      @ requires generateurCourant != null && faceCourante != null;
      @ ensures \fresh(\result);
      @ ensures \result.size() ==  faceCourante.size();
      @ ensures (\forall int i; i >= 0 && i < \result.size();
      @                        \result.get(i) instanceof Intent
      @                        && ((Intent) \result.get(i)).containsAll(generateurCourant));
      @ pure
      @*/
    public List<Intent> computeNewLockers(Intent generateurCourant,
                                    Intent faceCourante) {
        // Parcours de l'ensemble des faces
        List<Intent> resultat = new ArrayList<Intent>(faceCourante.size());
        for (FormalAttribute itemFace : faceCourante) {
            Intent bloqueur  = generateurCourant.clone();
            // Ajout du nouveau générateur (union du générateur courant avec la
            // face courante)
            bloqueur.add(itemFace);
            resultat.add(bloqueur);
        }
        return resultat;
    }

    /**
     * Calcul des générateurs pour le noeud spécifié
     * 
     * @param node
     * @return
     */
    /*@
      @ requires node != null;
      @
      @*/
    public List<Intent> computeNodeGenerators(Node<Concept> node) {
        Concept concept = node.getContent();
        Intent intent = concept.getIntent();
        if (!intent.isEmpty()) {
            LinkedList<Intent> faceList = computeFacesOfNode(node);
            if (!faceList.isEmpty()) {
                // Sélection de la première face et initialisation de l'ensemble
                // des générateurs
                Intent premiereFace = faceList.removeFirst();
                List<Intent> ensembleGenerateur = getSingletonList(premiereFace);

                if (!faceList.isEmpty()) {
                    for (Intent faceCourante : faceList) {
                        // Calcul de l'ensemble des générateurs du noeud courant
                        ensembleGenerateur = modificationGenerateurs(faceCourante,
                                ensembleGenerateur);
                    }
                } 
                concept.setGenerator(ensembleGenerateur);
            } else {
                // Les générateurs du noeud courant correspondent a l'ensemble
                // des items de l'intent du noeud courant
                concept.setGenerator(getSingletonList(intent));
            }
        }
        return concept.getGenerator();
    }

    /**
     * Calcul des générateurs pour l'ensemble des noeuds du treillis
     */
    public void computeLatticeGenerators() {

        int nbMaxNode = myLattice.size();
        int numNodeCurrent = 1;

        // Parcours de l'ensemble des fermés
        Iterator<Node<Concept>> it = myLattice.iterator();
        List<Intent> resultat = null;
        while (it.hasNext()) {
            // Sélection du noeud courant
            Node<Concept> noeudCourant = it.next();

            // Calcul de son ensemble de générateurs
            resultat = computeNodeGenerators(noeudCourant);
            
            // Incrémentation du nombre de générateurs
            nombreGenerateurs += resultat.size();
            numNodeCurrent++;
            sendJobPercentage((numNodeCurrent * 100) / nbMaxNode);
            if (numNodeCurrent >= (nbMaxNode - 5)) {
                System.out.println("Jen(" + numNodeCurrent + "): last node nb generateurs=" + nombreGenerateurs);
                if (numNodeCurrent == nbMaxNode) {
                    if (it.hasNext()) {
                        System.out.println("Jen(last): skipping last (bottom) node");   
                        it.next();
                    }
                }
            } else { 
                if (numNodeCurrent % 10 == 0) {
                    System.out.println("Jen(" + numNodeCurrent + "): nb generateurs=" + nombreGenerateurs);
                }
            }
        }
    }

    /**
     * Renvoie la liste des éléments de listeBloqueurs qui sont bloqués par
     * au moins un élément de la liste bloqueursMinimaux.
     * Un bloqueur est dit bloqué s'il contient un des bloqueurs minimaux de
     * la liste spécifiée.
     * 
     * @param listeBloqueurs
     * @param bloqueursMinimaux
     * @return
     */
    /*@
      @ requires listeBloqueurs != null;
      @ requires (\forall int i; i >= 0 && i < listeBloqueurs.size();
      @                         listeBloqueurs.get(i) instanceof Intent);
      @ requires bloqueursMinimaux != null;
      @ requires (\forall int i; i >= 0 && i < bloqueursMinimaux.size();
      @                         bloqueursMinimaux.get(i) instanceof Intent);
      @ ensures \result != null;
      @ ensures listeBloqueurs.containsAll(\result);
      @ ensures (\forall int i; i >= 0 && i < \result.size();
      @                 \result.get(i) instanceof Intent
      @                 && (\exists int iMin; iMin >= 0 && iMin < bloqueursMinimaux.size();
      @                             ((Intent) \result.get(i)).containsAll(((Intent) bloqueursMinimaux.get(iMin)))));
      @ ensures (\forall int i; i >= 0 && i < listeBloqueurs.size() && !\result.contains(listeBloqueurs.get(i));
      @                  (\forall int iMin; iMin >= 0 && iMin < bloqueursMinimaux.size();
      @                             !((Intent) listeBloqueurs.get(i)).containsAll(((Intent) bloqueursMinimaux.get(iMin)))));
      @ pure
      @*/
    public List<Intent> selectLockedBlocker(List<Intent> listeBloqueurs,
                                  List<Intent> bloqueursMinimaux) {
        List<Intent> resultat = new ArrayList<Intent>(listeBloqueurs.size());
        for (Intent bloqueurCourant : listeBloqueurs) {
            Iterator<Intent> iterMinBloqueurs = bloqueursMinimaux.iterator();
            boolean bloqueurCourantBloque = false;
            while (iterMinBloqueurs.hasNext() && !bloqueurCourantBloque) {
                Intent minBloqueur = iterMinBloqueurs.next();
                if (bloqueurCourant.containsAll(minBloqueur)) {
                    resultat.add(bloqueurCourant);
                    bloqueurCourantBloque = true;
                }
            }
        }
        return resultat;
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.util.tooltask.JobObservable#getDescription()
     */
    public String getDescription() {
        return "Jen for generator computation";
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Runnable#run()
     */
    public void run() {
        computeLatticeGenerators();
        if (jobObserv != null)
            jobObserv.jobEnd(true);
    }


    /**
     * @return Returns the nombreGenerateurs.
     */
    /*@
      @ pure
      @*/
    public int getNbGenerateurs() {
        return nombreGenerateurs;
    }

    /**
     * @return Returns the myLattice.
     */
    /*@
      @ pure
      @*/
    public CompleteConceptLattice getLattice() {
        return myLattice;
    }

}
