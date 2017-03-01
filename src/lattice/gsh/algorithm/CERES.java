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

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import lattice.algorithm.LatticeAlgorithm;
import lattice.alpha.util.BGConceptNode;
import lattice.util.concept.Concept;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;
import lattice.util.structure.LatticeGraph;
import lattice.util.structure.Node;

/**
 * @author Mr ROUME To change this generated comment edit the template variable
 *         "typecomment": Window>Preferences>Java>Templates. To enable and
 *         disable the creation of type comments go to
 *         Window>Preferences>Java>Code Generation.
 */
public class CERES extends LatticeAlgorithm {

    /**
     * Constructor for CERES.
     */
    public CERES() {
        super();
    }

    /**
     * Constructor for CERES.
     * 
     * @param bRel
     */
    public CERES(MatrixBinaryRelationBuilder bRel) {
        super(bRel);
    }

    /**
     * @see LatticeAlgorithm#doAlgorithm()
     */
    public void doAlgorithm() {
        AlgoPrincipale();

        // Suppression du Top si un sommet crée est aussi un top
        if (getLattice().getTop().getChildren().size() == 1
            && getLattice().getTop().getContent().getExtent().size() == 0
            && getLattice().getTop().getContent().getIntent().size() == 0) {
            ConceptNode nouvTop = (ConceptNode) getLattice().getTop()
                    .getChildren().get(0);
            Node<Concept> ancTop = getLattice().getTop();
            nouvTop.removeParent(ancTop);
            ancTop.removeChild(nouvTop);
            getLattice().setTop(nouvTop);
        }

        // Mise ne place du Bottom
        ((LatticeGraph) getLattice()).findNSetBottom();

        getBinaryRelation().setLattice(getLattice());
    }

    /**
     * @see JobObservable#getDescription()
     */
    public String getDescription() {
        return "CERES";
    }

    private void AlgoPrincipale() {
        setLattice(new LatticeGraph());
        Extent ext = new SetExtent();
        for (int i = 0; i < getBinaryRelation().getObjectsNumber(); i++) {
            ext.add(getBinaryRelation().getFormalObject(i));
        }
        getLattice()
                .setTop(new ConceptNodeImp(new ConceptImp(ext, new SetIntent())));

        // Debut Algo
        List<Concept> lesPreConcepts = new Vector<Concept>(getBinaryRelation()
                .getInitialAttributePreConcept(MatrixBinaryRelationBuilder.DS_EXTENT_SORTED));
        Intent SOP = new SetIntent(); // L'ensemble des FormalObject deja
                                            // insere dans le graph
        for (int i = 0; i < lesPreConcepts.size(); i++) {
            List<ConceptNode> PLN = new Vector<ConceptNode>();
            Concept c = lesPreConcepts.get(i);
            int extentSize = c.getExtent().size();
            int k = i;
            do {
                boolean trouve = false;
                for (int j = 0; !trouve && j < PLN.size(); j++) {
                    ConceptNode N = PLN.get(j);
                    if (N.getContent().getExtent().equals(c.getExtent())) {
                        N.getContent().getIntent().addAll(c.getIntent());
                        trouve = true;
                    }
                }
                if (!trouve) {
                    // Remplissage du RPs LP a deja ete fait (-Preconcept-) !
                    c.getIntent().addAll(c.getIntent());
                    ConceptNode N = new BGConceptNode(c);
                    PLN.add(N);
                }
                k++;
            } while (k < lesPreConcepts.size()
                     && (c = (lesPreConcepts.get(k)))
                             .getExtent().size() == extentSize);

            // car i++ se fera a la fin de la boucle for
            i = k - 1;

            for (int j = 0; j < PLN.size(); j++) {
                ConceptNode N =  PLN.get(j);
                // Remplissage de RP
                N.getContent().getIntent().addAll(N.getContent().getIntent());

                Classify( N, SOP, true);

                // Mise a Jour de SOP
                SOP.addAll(N.getContent().getIntent());

                // Mise a Jour de LPs
                for (Iterator it = N.getContent().getExtent().iterator(); it
                        .hasNext();) {
                    FormalObject o = (FormalObject) it.next();
                    // if(binRel.getF(o).size()==N.getConcept().getIntent().size())
                    // N.getConcept().getSimplifyExtent().add(o);
                    if (getBinaryRelation().getIntent(o).equals(N.getContent().getIntent()))
                        N.getContent().getExtent().add(o);
                }

                WorkOnLeftPart(N, SOP);
            }

            sendJobPercentage((i * 100) / lesPreConcepts.size());
        }
        // Fin Algo

    }

    private void Classify(Node<Concept> N, Intent SOP, boolean nodeOfOp) {
        List<Node<Concept>> Q = new Vector<Node<Concept>>(); // File accueillant des noeuds
                                    // potentiellement parent de N
        List<Node<Concept>> DSC = new Vector<Node<Concept>>(); // un ensemble de parents de N
        Q.add(getLattice().getTop()); // Q recoit top en initialisation
        Node<Concept> CSC = null;
        while (Q.size() != 0) {
            CSC =  Q.remove(0);
            DSC.add(CSC);
            for (Node<Concept> parent : CSC.getParents()) {
                DSC.remove(parent);
                // DSC doit contenir uniquement des parents directs
            }
            
            for (Node<Concept> child : CSC.getChildren()) {
                 if (child.getDegre() == -1) {
                    child.setDegre(child.getParents().size());
                }
                child.setDegre(child.getDegre() - 1);
                if (child.getDegre() == 0) {
                    child.setDegre(-1);
                    if (N.getContent().getExtent()
                            .extentUnion(child.getContent().getExtent())
                            .equals(child.getContent().getExtent())) {
                        Q.add(child);
                        if (nodeOfOp) {
                            for (FormalAttribute attr : child.getContent().getIntent()) {
                                 N.getContent().getIntent().add(attr);
                            }
                        }
                    }
                }
            }

        }
        ((LatticeGraph) getLattice()).add(N);
        // System.out.println(N.getConcept().toString());
        for (int i = 0; i < DSC.size(); i++) {
            N.addParent( DSC.get(i));
            DSC.get(i).addChild(N);
        }

    }

    private void WorkOnLeftPart(Node<Concept> Nod, Intent SOP) {
        Extent CC = (Extent) Nod.getContent().getExtent().clone();
        for (Iterator it = Nod.getContent().getExtent().iterator(); it
                .hasNext();) {
            CC.remove(it.next());
        }
        List<FormalObject> lesObjsTrie = new Vector<FormalObject>();
        for (FormalObject fobj : CC) {
            int tailleFe = getBinaryRelation().getIntent(fobj).size();
            boolean trouve = false;
            for (int i = 0; i < lesObjsTrie.size() && !trouve; i++) {
                FormalObject o = lesObjsTrie.get(i);
                int tailleFo = getBinaryRelation().getIntent(o).size();
                if (tailleFe <= tailleFo) {
                    lesObjsTrie.set(i, fobj);
                    trouve = true;
                }
            }
            if (!trouve)
                lesObjsTrie.add(fobj);
        }
        // Ici lesObjsTrie est l'ensemble de e de CC trie par f croissant

        for (int i = 0; i < lesObjsTrie.size(); i++) {
            FormalObject e = lesObjsTrie.get(i);
            if (getBinaryRelation().getIntent(e).intentUnion(SOP).equals(SOP)) {
                // f(e) inclue dans SOP -> generation d'un element de Oc/Op

                // Creation d'un nouveau neud
                Extent LP = new SetExtent();
                LP.add(e);
                Intent RP = new SetIntent();
                RP.addAll(getBinaryRelation().getIntent(e));
                ConceptImp c = new ConceptImp(LP, RP);
                c.getExtent().add(e);
                ConceptNodeImp N = new ConceptNodeImp(c);
                for (int j = i + 1; j < lesObjsTrie.size(); j++) {
                    FormalObject cc = lesObjsTrie.get(j);
                    if (getBinaryRelation().getIntent(cc).size() == getBinaryRelation().getIntent(e).size()) {
                        if (getBinaryRelation().getIntent(cc).equals(getBinaryRelation().getIntent(e))) {
                            N.getContent().getExtent().add(cc);
                            lesObjsTrie.remove(cc);
                            // Comme il y a un retrait il faut re-ajouster le
                            // compteur
                            j--;
                        }
                    } else {
                        if (getBinaryRelation().getIntent(cc).intentUnion(getBinaryRelation().getIntent(e))
                                .equals(getBinaryRelation().getIntent(cc))) {
                            N.getContent().getExtent().add(cc);
                        }
                    }
                }
                Classify(N, SOP, false);
            }
        }

    }

}
