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

package lattice.gsh.algorithm;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import lattice.algorithm.LatticeAlgorithm;
import lattice.gui.tooltask.JobObservable;
import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.GagciRelationalAttribute;
import lattice.util.concept.Intent;
import lattice.util.concept.InterObjectBinaryRelationAttribute;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.structure.ConceptNodeImp;
import lattice.util.structure.LatticeGraph;
import lattice.util.structure.Node;

/**
 * @author Mr ROUME To change this generated comment edit the template variable
 *         "typecomment": Window>Preferences>Java>Templates. To enable and
 *         disable the creation of type comments go to
 *         Window>Preferences>Java>Code Generation.
 */
public class Gagci extends LatticeAlgorithm {

    MatrixBinaryRelationBuilder classRel;

    MatrixBinaryRelationBuilder assocRel;

    InterObjectBinaryRelation[] lesIORel;

    LatticeGraph classLG;

    boolean isClassLGModif = false;

    LatticeGraph assocLG;

    boolean isAssocLGModif = false;

    /**
     * Constructor for Gagci.
     */
    public Gagci() {
        super();
    }

    /**
     * Constructor for Gagci.
     * 
     * @param bRel
     */
    public Gagci(MatrixBinaryRelationBuilder cRel, MatrixBinaryRelationBuilder aRel,
                 InterObjectBinaryRelation[] iobr) {
        super(cRel);
        classRel = cRel;
        assocRel = aRel;
        lesIORel = iobr;
    }

    /**
     * @see LatticeAlgorithm#doAlgorithm()
     */
    public void doAlgorithm() {
        execAlgo();
        jobObserv.jobEnd(true);
    }

    /**
     * @see JobObservable#getDescription()
     */
    public String getDescription() {
        return "GAGCI - incremental MultiFCA using GSH";
    }

    public void execAlgo() {

        // Creation du premier trellis
        LatticeAlgorithm algo = new CERES(classRel);
        if (jobObserv != null)
            jobObserv.setTitle(getDescription() + " - 1st step CERES on Class");
        algo.setJobObserver(jobObserv);
        algo.doAlgorithm();
        if (jobObserv != null)
            jobObserv.setPercentageOfWork(100);
        // ... pour les classes
        classLG = (LatticeGraph) algo.getLattice();
        algo = new CERES(assocRel);
        if (jobObserv != null)
            jobObserv.setPercentageOfWork(0);
        if (jobObserv != null)
            jobObserv.setTitle(getDescription()
                               + " - 1st step CERES on Assocation");
        algo.setJobObserver(jobObserv);
        algo.doAlgorithm();
        if (jobObserv != null)
            jobObserv.setPercentageOfWork(100);
        // ... pour les associations
        assocLG = (LatticeGraph) algo.getLattice();

        // Des vecteur stoquant se qui est nouveau dans classLG et assocLG
        List<Node<Concept>> newClassNodes;
        newClassNodes = new ArrayList<Node<Concept>>(classLG.getAllNodes());
        newClassNodes.remove(classLG.getTop());
        newClassNodes.remove(classLG.getBottom());
        List<Node<Concept>> newAssocNodes;
        newAssocNodes = new ArrayList<Node<Concept>>(assocLG.getAllNodes());
        newAssocNodes.remove(assocLG.getTop());
        newAssocNodes.remove(assocLG.getBottom());

        FormalObject[] classObjs = classRel.getFormalObjects();
        FormalObject objC;
        FormalObject[] assocObjs = assocRel.getFormalObjects();
        // Structure de traitement:
        Iterator it = null;
        Iterator it2 = null;
        Vector Q = null;
        Node<Concept> N = null;
        Node<Concept> child = null;
        Extent lesObjRel;
        Intent lesAttRel;
        Extent[] newE = new SetExtent[lesIORel.length];
        Intent singleInt = null;
        List<Concept> lesPreconcepts = new Vector<Concept>();
        boolean premierTour = true;
        // Tant que le point fixe n'est pas atteint
        int nbIter = 0;
        while (newClassNodes.size() != 0 || newAssocNodes.size() != 0) {

            // --- Enrichir les classes en fonction des relations

            // Creation des preconcept
            lesPreconcepts.clear();
            for (int i = 0; i < newAssocNodes.size(); i++) {
                N = newAssocNodes.get(i);

                for (int j = 0; j < lesIORel.length; j++)
                    newE[j] = new SetExtent();

                // On parcours toutes l'extension de chaque concept
                // Afin de creer un preconcept relationel pour chaque relation
                for (FormalObject objA : N.getContent().getExtent()) {
                    // Pour chaque relation creation des extenstions associé au
                    // noeud courant
                     for (int j = 0; j < lesIORel.length; j++) {
                        lesObjRel = lesIORel[j]
                                .getExtent(new InterObjectBinaryRelationAttribute(
                                                                             objA));
                        newE[j] = newE[j].extentUnion(lesObjRel);
                    }
                }
                for (int j = 0; j < lesIORel.length; j++) {
                    if (newE[j].size() != 0) {
                        singleInt = new SetIntent();
                        // creation d'une intension d'un preconcept relationel
                        singleInt
                                .add(new GagciRelationalAttribute(
                                                                  lesIORel[j],
                                                                  N
                                                                          .getContent()));
                        // creation du preconcept
                        Concept newC = new ConceptImp(newE[j], singleInt);
                        for (FormalAttribute attr : singleInt) {
                            newC.getIntent().add(attr);
                        }
                        lesPreconcepts.add(newC);
                    }
                }
            }

            // --- Enrichir les associations en fonction des classes
            if (premierTour) {
                newClassNodes.addAll(incremente(classLG, lesPreconcepts));
                premierTour = false;
            } else
                newClassNodes = incremente(classLG, lesPreconcepts);

            // Creation des preconcept
            lesPreconcepts.clear();
            for (int i = 0; i < newClassNodes.size(); i++) {
                N = newClassNodes.get(i);

                for (int j = 0; j < lesIORel.length; j++)
                    newE[j] = new SetExtent();

                // On parcours toutes l'extension de chaque concept
                for (FormalObject objA : N.getContent().getExtent()) {
                    // Toutes les classes en relation avec une assoc contenue
                    // dans l'extent de N
                    // sont en relation avec le concept porte par N
                    for (int j = 0; j < lesIORel.length; j++) {
                        lesAttRel = lesIORel[j].getIntent(objA);
                        lesObjRel = new SetExtent();
                        for (it2 = lesAttRel.iterator(); it2.hasNext();)
                            lesObjRel
                                    .add(((InterObjectBinaryRelationAttribute) it2
                                            .next()).getObject());
                        newE[j] = newE[j].extentUnion(lesObjRel);
                    }
                }
                for (int j = 0; j < lesIORel.length; j++) {
                    if (newE[j].size() != 0) {
                        singleInt = new SetIntent();
                        singleInt
                                .add(new GagciRelationalAttribute(
                                                                  lesIORel[j],
                                                                  N
                                                                          .getContent()));
                        lesPreconcepts.add(new ConceptImp(newE[j], singleInt));
                    }
                }
            }

            // --- Enrichir les associations en fonction des classes
            newAssocNodes = incremente(assocLG, lesPreconcepts);

            nbIter++;
            System.out.println("nbIter=" + nbIter);
        }

        setLattice(classLG);
    }     

    private List<Node<Concept>> incremente(LatticeGraph aGraph,
                                         List<Concept> lesPreconcepts) {

        if (jobObserv != null)
            jobObserv.setTitle(getDescription() + " - Increment");
        sendJobPercentage(0);

        List<Node<Concept>> newNodes = new Vector<Node<Concept>>(lesPreconcepts
                .size(), 0);

        List<Node<Concept>> lesSupC = new Vector<Node<Concept>>(aGraph
                .getAllNodes().size(), 0); // un ensemble de parents de N
        List<Node<Concept>> lesInfC = new Vector<Node<Concept>>(aGraph
                .getAllNodes().size(), 0); // un ensemble de parents de N

        List<Node<Concept>> Q = new Vector<Node<Concept>>(); // File accueillant
                                                            // des noeuds
                                                            // potentiellement
                                                            // parent de N
        for (int i = 0; i < lesPreconcepts.size(); i++) {
            Concept C = lesPreconcepts.get(i);
            System.out.println("Insertion de : " + C.toString());

            // Recherche des SupC
            lesSupC.clear();
            Q.clear();
            Q.add(aGraph.getTop()); // Q recoit top en
                                                // initialisation
            Node<Concept> CSC = null;
            Node<Concept> child = null;
            ((ConceptNodeImp) aGraph.getTop()).resetDegre();
            while (Q.size() != 0) {
                CSC = (ConceptNodeImp) Q.remove(0);
                lesSupC.add(CSC);
                for (Iterator it = CSC.getParents().iterator(); it.hasNext();) {
                    lesSupC.remove(it.next());
                    // DSC doit contenir uniquement les parents directs
                }
                for (Iterator it = CSC.getChildren().iterator(); it.hasNext();) {
                    child = (ConceptNodeImp) it.next();
                    if (child.getDegre() == -1)
                        child.setDegre(child.getParents().size());
                    child.setDegre(child.getDegre() - 1);
                    if (child.getDegre() == 0) {
                        child.setDegre(-1);
                        if (child != aGraph.getBottom()
                            && child.getContent().getExtent()
                                    .extentUnion(C.getExtent())
                                    .equals(child.getContent().getExtent())) {
                            Q.add(child);
                        }
                    }
                }
            }
            System.out.println("LesSupC = " + lesSupC + "\n");

            // Recherche des InfC
            lesInfC.clear();
            Q.clear();
            Q.add(aGraph.getBottom()); // Q recoit bot en
                                                    // initialisation
            CSC = null;
             aGraph.getTop().resetDegre();
            while (Q.size() != 0) {
                CSC = Q.remove(0);
                lesInfC.add(CSC);
                for (Iterator it = CSC.getChildren().iterator(); it.hasNext();) {
                    lesInfC.remove(it.next());
                    // lesInfC doit contenir uniquement les Enfants directs
                }
                // On ajoute a tous les Inf de C l'intents de C
                CSC.getContent().getIntent().addAll(C.getIntent());
                
                for (Node<Concept> pere : CSC.getParents()) {
                    if (pere.getDegre() == -1)
                        pere.setDegre(pere.getChildren().size());
                    pere.setDegre(pere.getDegre() - 1);
                    if (pere.getDegre() == 0) {
                        pere.setDegre(-1);
                        if (pere != aGraph.getTop()
                            && C.getExtent().extentUnion(
                                                         pere.getContent()
                                                                 .getExtent())
                                    .equals(C.getExtent())) {
                            Q.add(pere);
                        }
                    }
                }

            }

            System.out.println("LesInfC = " + lesInfC + "\n");

            if (lesSupC.size() == 1 && lesInfC.size() == 1
                && lesSupC.get(0) == lesInfC.get(0)) {
                for (Iterator it = C.getIntent().iterator(); it.hasNext();) {
                    FormalAttribute fa = (FormalAttribute) it.next();
                    lesSupC.get(0).getContent()
                            .getIntent().add(fa);
                }
            } else {

                // Suprimer les liens allant des SupC vers les InfC et vis versa
                for (Node<Concept> pere : lesSupC) {
                    for (int k = 0; k < lesInfC.size(); k++) {
                        child = lesInfC.get(k);
                        child.removeParent(pere);
                        pere.removeChild(child);
                    }
                }

                Node<Concept> N = new ConceptNodeImp(C);
                // Accrochage sur les parents
                for (Node<Concept> pere : lesSupC) {
                    N.addParent(pere);
                    pere.addChild(N);
                    for (Iterator it = pere.getContent().getExtent().iterator(); it
                            .hasNext();) {
                        FormalObject fo = (FormalObject) it.next();
                        // Faire descendre dans le nouveau concept les elements
                        // de l'extension simplifie si necessaire
                        if (C.getExtent().contains(fo)) {
                            C.getExtent().add(fo);
                        }
                    }
                    // suprimer les elements de l'extension simplifie si
                    // necessaire
                    for (Iterator it = C.getExtent().iterator(); it.hasNext();) {
                        FormalObject fo = (FormalObject) it.next();
                        pere.getContent().getExtent().remove(fo);
                    }
                    // Mise a jour de l'intension
                    for (Iterator it = pere.getContent().getIntent().iterator(); it
                            .hasNext();) {
                        FormalAttribute fa = (FormalAttribute) it.next();
                        C.getIntent().add(fa);
                    }
                }
                // Acrochage sur les enfants
                for (int j = 0; j < lesInfC.size(); j++) {
                    child = lesInfC.get(j);
                    child.addParent(N);
                    N.addChild(child);
                }

                newNodes.add(N);
            }

            sendJobPercentage((i * 100) / lesPreconcepts.size());
        }
        sendJobPercentage(100);
        return newNodes;
    }

}
