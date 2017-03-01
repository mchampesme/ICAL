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
 * Created on 2003-12-16 To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package lattice.algorithm.rca;

import java.util.Hashtable;
import java.util.Iterator;
import java.util.Vector;

import lattice.gui.MultiFCASettingsView;
import lattice.gui.controller.RCAController;
import lattice.gui.graph.LatticeGraphFrame;
import lattice.util.concept.AbstractFormalAttributeValue;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.structure.CompleteConceptLattice;

/**
 * @author rouanehm (Amine Mohamed ROUANE-HACENE) To change the template for
 *         this generated type comment go to
 *         Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */

public class MultiFCA {

    LatticeFamily workingRCF; // current working set of relational context

    RCAController rcaControler;

    // stores object-valued attribute (ova) within their corresponding
    // relational scale
    // i.e., relational scale along the relation ova
    Hashtable ovaRelationalExtension;

    // for each relation ova, we store an iterator on the corresponding encoding
    // structure
    // which could be lattice, GSH or simply concept family
    // at the end of each iteration nextEncodingStruct is assigned to
    // currentEncodingStruct;
    Hashtable currentEncodingStruct;

    // for each context we store the set of concepts that will be used to scale
    // relations (ova)
    // which point to that context in the next iteration
    Hashtable nextEncodingStruct;

    public MultiFCA(RCAController rcaControler) {
        this.rcaControler = rcaControler;
        workingRCF = new LatticeFamily(rcaControler.getRCF());
        ovaRelationalExtension = new Hashtable();
        nextEncodingStruct = new Hashtable();
        currentEncodingStruct = new Hashtable();
    }

    /*
     * (non-Javadoc)
     * 
     * @see lattice.algorithm.LatticeAlgorithm#doAlgorithm()
     */
    public void run() {
        rcaControler.sendConsoleMessage("Processing RCF...!\n");
        //
        // !------------------------------------------------------------!
        // ! scheduled steps (as described in ICG ICCS'2004 paper) are: !
        // ! 1- scaling many-valued attributes (but relational ones) !
        // ! 2- compute initial lattices !
        // ! 3- scaling relational attributes !
        // ! 4- compute relational lattices !
        // ! 5- redo steps 3+4 until a fixpoint is reached !
        // !------------------------------------------------------------!
        //
        // Step 1: non relational but many-valued attributes are scaled
        rcaControler
                .sendConsoleMessage("Conceptual scaling of MV contexts in working RCF...");
        for (int i = 0; i < workingRCF.getWorkingContextSet().size(); i++) {
            RelationBuilder currentRel = (RelationBuilder) workingRCF
                    .getWorkingContext(i);
            // scale only MV contexts which were selected to be in the RCF
            if (!MultiFCASettingsView.getSelectedContexts()
                    .contains(currentRel.getName()))
                continue;
        }// for
        rcaControler
                .sendConsoleMessage("Conceptual Scaling of working RCF is over.");

        // step 2: compute initial lattices
        rcaControler.sendConsoleMessage("Computing initial lattice graphs...");
        workingRCF.computeInitialLatticeGraphs();
        initializeEncodingStructures();

        // Step 3: In the following we perform the core tasks of Multi-FCA
        // algorithm which alternates between relational scaling
        // and lattice construction

        boolean fixpoint = false;
        int iteration = 1;
        Vector eliminatedWorkingCtx = new Vector();
        // bellow is the core of the MultiFCA iterative method
        // the method iterates while a fixpoint is not reached
        while (!fixpoint) {
            fixpoint = true;
            rcaControler.sendConsoleMessage("Multi-FCA iterartion number ");
            rcaControler.sendConsoleMessage(Integer.toString(iteration));
            System.out.println("Multi-FCA iterartion number "
                               + Integer.toString(iteration));
            updateEncodingStructures();
            for (int i = 0; i < workingRCF.getWorkingContextSet().size(); i++) {
                RelationBuilder ctx = (RelationBuilder) workingRCF
                        .getWorkingContextSet().elementAt(i);
                rcaControler
                        .sendConsoleMessage("Computing relational extension of working context: "
                                            + ctx.getName());
                Vector ovaSet = workingRCF.getOVASet(ctx);
                if (ovaSet.size() > 0) {
                    // compute new relational extention for each ova in the
                    // context ctx
                    this.computeRelExtension(ovaSet, iteration);
                    // compute the relational extention of the current context
                    // by merging the relational extension along each ova
                    MatrixBinaryRelationBuilder newCtxRelExt = extend_Rel(ctx, ovaSet);
                    // convert the abstract context to a binary context
                    MatrixBinaryRelationBuilder derivedCtx = null;
                    if (ctx instanceof MatrixBinaryRelationBuilder)
                        derivedCtx = (MatrixBinaryRelationBuilder) ctx;
                   // store the number of concept before completing the context
                    int previousNUmberOfConcept = derivedCtx.getLattice()
                            .size();
                    // add the new relational extention (newCtxRelExt) to the
                    // existing context and update the corresponding lattice
                    // the method use an incremental-attribute lattice update
                    // algorithm
                    updateContext(derivedCtx, newCtxRelExt);
                    MatrixBinaryRelationBuilder derivedCtxCopy = (MatrixBinaryRelationBuilder) derivedCtx
                            .clone();

                    if (derivedCtx.getLattice().size() != previousNUmberOfConcept) {
                        fixpoint = false;
                        derivedCtxCopy.setName(ctx.getName()
                                                       + "-step-" + iteration);
                        // send the context and its lattice to the editor
                        // rcaControler.getRelationalContextEditor().addBinaryRelation(derivedCtxCopy);
                        // derivedCtx.getLattice().fillSimplified();
                        // LatticeGraphFrame f = new LatticeGraphFrame("Lattice
                        // of "+ctx.getRelationName()+" at step
                        // "+iteration,derivedCtx.getLattice().getTopConceptNode());
                        // f.show();
                    } else {
                        derivedCtxCopy.setName(ctx.getName()
                                                       + "-final");
                        // rcaControler.getRelationalContextEditor().addBinaryRelation(derivedCtxCopy);
                        System.out.println("Obtaining final lattice : "
                                           + derivedCtxCopy.getName());
                        // derivedCtx.getLattice().fillSimplified();
                        // if(MultiFCASettingsView.getSelectedRelationalLabeling()==MultiFCASettingsView.getReducedRelationalLabeling())
                        // RelationalLattice.removeRedundantLinks(rcaControler.getRCF(),derivedCtx);
                        // LatticeGraphFrame f = new LatticeGraphFrame("Final
                        // Lattice of
                        // "+ctx.getRelationName(),derivedCtx.getLattice().getTopConceptNode());
                        // f.show();
                        eliminatedWorkingCtx.add(ctx);
                    }
                }// if(ovaSet.size()>0)
                else {
                    // ctx.getLattice().fillSimplified();
                    // if(MultiFCASettingsView.getSelectedRelationalLabeling()==MultiFCASettingsView.getReducedRelationalLabeling())
                    // RelationalLattice.removeRedundantLinks(rcaControler.getRCF(),ctx);
                    // LatticeGraphFrame f = new LatticeGraphFrame("Final
                    // Lattice of
                    // "+ctx.getRelationName(),ctx.getLattice().getTopConceptNode());
                    // f.show();
                    System.out.println("Obtaining final lattice : "
                                       + ctx.getName());
                    eliminatedWorkingCtx.add(ctx);
                }
            }// external for

            for (int j = 0; j < eliminatedWorkingCtx.size(); j++) {
                workingRCF
                        .removeContext((RelationBuilder) eliminatedWorkingCtx
                                .elementAt(j));
                eliminatedWorkingCtx.remove(j);
            }
            iteration++;
        }// while(!fixpoint)
        rcaControler
                .sendConsoleMessage("Fixpoint is reached, Multi-FCA algorithm stopped...");
        System.out
                .println("Fixpoint is reached, Multi-FCA algorithm stopped...");
        workingRCF.displayFinalLattices();
    }// run

    /**
     * @param relation
     * @param newCtxRelExt
     */
    private void updateContext(MatrixBinaryRelationBuilder ctx,
                               MatrixBinaryRelationBuilder newCtxRelExt) {
        Vector createdConcepts = new Vector();
        for (int i = 0; i < newCtxRelExt.getAttributesNumber(); i++) {
            FormalAttribute fa;
            fa = newCtxRelExt.getFormalAttribute(i);
            Vector newAddedConcepts = AttributeLatticeUpdate
                    .addAttribute(ctx, fa, newCtxRelExt.getExtent(fa));
            createdConcepts.addAll(newAddedConcepts);
        }
        nextEncodingStruct.remove(ctx);
        nextEncodingStruct.put(ctx, createdConcepts);
    }

    /**
     * 
     */
    private void initializeEncodingStructures() {
        // at the begining, ova are scaled using complete lattices
        // later, the new created concept during lattice update are used.
        for (int i = 0; i < workingRCF.getWorkingContextSet().size(); i++) {
            RelationBuilder ctx = workingRCF.getWorkingContext(i);
            MatrixBinaryRelationBuilder derivedCtx = null;
            if (ctx instanceof MatrixBinaryRelationBuilder)
                derivedCtx = (MatrixBinaryRelationBuilder) ctx;
            nextEncodingStruct.put(derivedCtx, getConceptVector(derivedCtx
                    .getLattice()));
        }
    }

    private void updateEncodingStructures() {
        // updating the encoding structure to each object-valued attributes
        // (ova)
        // by the new created concept
        currentEncodingStruct.clear();
        for (int i = 0; i < workingRCF.getWorkingContextSet().size(); i++) {
            RelationBuilder ctx = workingRCF.getWorkingContext(i);
            MatrixBinaryRelationBuilder derivedCtx = null;
            if (ctx instanceof MatrixBinaryRelationBuilder)
                derivedCtx = (MatrixBinaryRelationBuilder) ctx;
            currentEncodingStruct.put(derivedCtx, nextEncodingStruct
                    .get(derivedCtx));
        }
    }

    /**
     * @param lattice
     * @return
     */
    private Vector getConceptVector(CompleteConceptLattice lattice) {
        Vector conceptVector = new Vector();
        Iterator it = lattice.iterator();
        while (it.hasNext())
            conceptVector.add(it.next());
        return conceptVector;
    }

    /**
     * @param ovaSet
     */
    private void computeRelExtension(Vector ovaSet, int iteration) {
        String ctxName = null;
        for (int j = 0; j < ovaSet.size(); j++) {
            InterObjectBinaryRelation rel = (InterObjectBinaryRelation) ovaSet
                    .elementAt(j);
            rcaControler
                    .sendConsoleMessage("Relational Scaling of the relational attribute: ");
            rcaControler.sendConsoleMessage(rel.getName());
            RelationBuilder objectsCtx = rcaControler.getRCF()
                    .getForName(rel.getObjectsContextName());
            RelationBuilder attributesCtx = rcaControler.getRCF()
                    .getForName(rel.getAttributesContextName());
            Vector encodingStruct = (Vector) currentEncodingStruct
                    .get(attributesCtx);
            if (encodingStruct == null) {
                rcaControler
                        .sendConsoleMessage("Encoding structure is missing...");
                return;
            }
            MatrixBinaryRelationBuilder relExtension = RelationalScale
                    .getRelationalscale((MatrixBinaryRelationBuilder) objectsCtx,
                                        (MatrixBinaryRelationBuilder) attributesCtx, rel,
                                        encodingStruct, MultiFCASettingsView
                                                .getSelectedEncodingSchema());

            relExtension.setName(rel.getName() + "-Step-"
                                         + iteration);
            // send the relational scale to the editor
            // rcaControler.getRelationalContextEditor().addBinaryRelation(relExtension);

            // replacing the relational extention of OVA rel
            ovaRelationalExtension.remove(rel);
            ovaRelationalExtension.put(rel, relExtension);
        }
    }

    /**
     * @param ctx
     * @param ovaSet
     */
    private MatrixBinaryRelationBuilder extend_Rel(RelationBuilder ctx, Vector ovaSet) {
        // the method merge the relational extension of all OVA (ovaSet) of a
        // given context ctx
        // in one complete binary context
        MatrixBinaryRelationBuilder relExt = new MatrixBinaryRelationBuilder(ctx.getName()
                                                   + getRelExtSuffix());
        // fill relExt formal objects using any OVA
        InterObjectBinaryRelation relAttr = (InterObjectBinaryRelation) ovaSet
                .elementAt(0);
        for (int i = 0; i < relAttr.getObjectsNumber(); i++)
            relExt.addObject(relAttr.getFormalObject(i));
        // fill relExt attribute using the ovaSET
        for (int i = 0; i < ovaSet.size(); i++) {
            relAttr = (InterObjectBinaryRelation) ovaSet.elementAt(i);
            MatrixBinaryRelationBuilder partialRelExt = (MatrixBinaryRelationBuilder) ovaRelationalExtension
                    .get(relAttr);
            complete(relExt, partialRelExt);
        }
        return relExt;
        // replacing the relational extention of context ctx
        // contextRelExtMap.remove(ctx);
        // contextRelExtMap.put(ctx,relExt);
    }

    /**
     * @return
     */
    private String getRelExtSuffix() {
        return "-RExtCtx";
    }

    /**
     * @param globalCtx
     * @param partialCtx
     * @return globalCtx=globalCtx+partialCtx
     */
    public void complete(MatrixBinaryRelationBuilder globalCtx,
                         MatrixBinaryRelationBuilder partialCtx) {
        if (partialCtx == null)
            return;
        if (globalCtx == null)
            return;
        for (int i = 0; i < partialCtx.getAttributesNumber(); i++) {
            FormalAttribute fa = partialCtx.getFormalAttribute(i);
            globalCtx.addAttribute(fa);
            for (int j = 0; j < globalCtx.getObjectsNumber(); j++) {
                try {
                    FormalObject fo = globalCtx.getFormalObject(j);
                    AbstractFormalAttributeValue fav = partialCtx
                            .getRelation(fo, fa);
                    globalCtx.setRelation(fo, fa, fav);
                } catch (BadInputDataException e1) {
                    rcaControler
                            .sendConsoleMessage("Binary context merge fatal error...");
                    e1.printStackTrace();
                }
            }// internal for
        }
    }

    /**
     * @return
     */
    private boolean checkFixpoint() {
        // check weather a fixpoint is reached or not
        // when lattice of a given context obtained at the step (i-1)
        // is isomorphic to the lattice obtained at the step (i)
        // this could ne also obtained by comparing family lattice sizes
        return true;
    }

    private void displayWorkingRCF() {
        // erreur workingRCF ne contient pas tous les contexts selected
        for (int i = 0; i < workingRCF.getWorkingContextSet().size(); i++) {
            RelationBuilder ctx = (RelationBuilder) workingRCF
                    .getWorkingContextSet().elementAt(i);
            MatrixBinaryRelationBuilder derivedCtx = null;
            if (ctx instanceof MatrixBinaryRelationBuilder)
                derivedCtx = (MatrixBinaryRelationBuilder) ctx;
            LatticeGraphFrame f = new LatticeGraphFrame(
                                                        "Final Lattice of "
                                                                + ctx
                                                                        .getName(),
                                                        derivedCtx.getLattice()
                                                                .getTop());
            f.show();
        }// for
    }

    public String getDescription() {
        return "MultiFCA - complete lattices version";
    }

}
