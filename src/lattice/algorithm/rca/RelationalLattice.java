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
 * Created on 2004-08-16 coding starts at 10:30 AM and ends at: 06:15 PM TODO To
 * change the template for this generated file go to Window - Preferences - Java -
 * Code Style - Code Templates
 */
package lattice.algorithm.rca;

import java.util.Iterator;
import java.util.Vector;

import lattice.util.concept.Concept;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import lattice.util.relation.RelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.Node;

/**
 * @author rouanehm TODO To change the template for this generated type comment
 *         go to Window - Preferences - Java - Code Style - Code Templates
 */
public class RelationalLattice {

    public static int FULL_INTENT = 0;

    public static int REDUCED_INTENT = 1;

    // class description:
    // this class helps reducing the relational labeling of lattices
    // obtained at the end of the MULTI-FCA algorithm.
    // the reduction consists in removing redundant links within concept intent
    // a link [ovaStem1-cNum1] within concept intent is considered as redundant
    // when there is another link [ovaStem2-cNum2] within the same intent
    // and [ovaStem1=ovaStem2, cNum1 is comparable to cNum2].
    // In this case, the minimal concept is kept.
    //

    public static void removeRedundantLinks(RelationalContextFamily fullRCF,
                                            RelationBuilder context) {
        System.out
                .println("Reduce relational labeling of final lattice associated to "
                         + context.getName().toString());
        Iterator family = context.getLattice().iterator();
        while (family.hasNext()) {
            ConceptNode conceptNode = (ConceptNode) family.next();
            // System.out.println("processing concept "+conceptNode.toString());
            reduce(fullRCF, context, conceptNode, FULL_INTENT);
        }
    }

    // targetIntent is either FULL_INTENT or REDUCED_INTENT
    public static void removeRedundantLinks(RelationalContextFamily fullRCF,
                                            RelationBuilder context,
                                            int targetIntent) {
        System.out
                .println("Reduce relational labeling of final lattice associated to "
                         + context.getName().toString());
        Iterator family = context.getLattice().iterator();
        while (family.hasNext()) {
            ConceptNode conceptNode = (ConceptNode) family.next();
            // System.out.println("processing concept "+conceptNode.toString());
            reduce(fullRCF, context, conceptNode, targetIntent);
        }
    }

    /**
     * @param concept
     */
    private static void reduce(RelationalContextFamily fullRCF,
                               RelationBuilder context,
                               ConceptNode conceptNode, int targetIntent) {
        Intent intent = null;
        if (targetIntent == FULL_INTENT)
            intent = conceptNode.getContent().getIntent();
        if (targetIntent == REDUCED_INTENT)
            intent = conceptNode.getContent().getIntent();

        // remove links form the intent
        Vector links = getConceptLinks(intent);
        Vector relAttrsData = getRelAttrsData(fullRCF, links);
        Vector minimas = getConceptMinimas(context, relAttrsData);
        // put new links into the concept intent
        replace(intent, links, minimas);
    }

    /**
     * @param intent
     * @return the relational attributes only
     */
    public static Vector getConceptLinks(Intent intent) {
        // returns [intent]-[derived context attributes]
        Vector links = new Vector();
        Iterator features = intent.iterator();
        while (features.hasNext()) {
            FormalAttribute feature = (FormalAttribute) features.next();
            if (relationalAttribute(feature))
                links.add(feature);
        }
        return links;
    }

    /**
     * @param feature
     * @return
     */
    public static boolean relationalAttribute(FormalAttribute feature) {
        // the rule used to rename a relational scaling property is as follow
        // ovaStem+"-c"+node.getId().toString()
        String featureName = feature.getName();
        // the following condition should be reenforced in near future
        if (featureName.indexOf(":c") > 0)
            return true;
        return false;
    }

    /**
     * @param links
     * @return their minima vector
     */
    private static Vector getRelAttrsData(RelationalContextFamily fullRCF,
                                          Vector links) {
        // the following vector is used to store relational attributes data
        // of elements in the argument variable 'links'
        Vector relAttrsData = new Vector();
        // computing the concepts ID
        Iterator it = links.iterator();
        while (it.hasNext()) {
            FormalAttribute fa = (FormalAttribute) it.next();
            String faName = fa.getName();
            // extract relation name
            String relName = faName.substring(0, faName.indexOf(":"));
            // extract context name
            // String
            // ctxName=faName.substring(faName.indexOf("-")+1,faName.indexOf("-c"));
            String ctxName = getTargetContext(relName, fullRCF);
            // extract concept id
            String nodeIDStr = faName.substring(faName.indexOf(":c") + 2);
            Integer nodeID = Integer.valueOf(nodeIDStr);
            relAttrsData.add(new RelationalAttributeData(fa, relName, ctxName,
                                                         nodeID));
        }
        // computing for each rel. attr. the lattice node
        for (int i = 0; i < relAttrsData.size(); i++) {
            RelationalAttributeData relAttr = (RelationalAttributeData) relAttrsData
                    .elementAt(i);
            RelationBuilder ctx = fullRCF
                    .getForName(relAttr.getContextName());
            if (ctx == null)
                System.out
                        .println("Unable to locate working context when reducing relational labeling...");
            Node<Concept> cn = ctx.getLattice().findNode(relAttr.getNodeID());
            if (cn == null) {
                System.out.println("Scaling concept not found!");
            } else
                relAttr.setConceptNode(cn);
        }
        return relAttrsData;
    }

    /**
     * @param relName
     * @param fullRCF
     * @return
     */
    private static String getTargetContext(String relName,
                                           RelationalContextFamily fullRCF) {
        InterObjectBinaryRelation rel = (InterObjectBinaryRelation) fullRCF
                .getForName(relName);
        RelationBuilder targetContext = fullRCF.getForName(rel
                .getAttributesContextName());
        return targetContext.getName();
    }

    public static RelationalAttributeData getRelAttrData(
                                                         RelationalContextFamily fullRCF,
                                                         FormalAttribute rfa) {
        String faName = rfa.getName();
        // extract relation name
        String relName = faName.substring(0, faName.indexOf(":"));
        // extract context name
        // String
        // ctxName=faName.substring(faName.indexOf("-")+1,faName.indexOf("-c"));
        String ctxName = getTargetContext(relName, fullRCF);
        // extract concept id
        String nodeIDStr = faName.substring(faName.indexOf(":c") + 2);
        Integer nodeID = Integer.valueOf(nodeIDStr);
        RelationalAttributeData relAttrData = new RelationalAttributeData(
                                                                          rfa,
                                                                          relName,
                                                                          ctxName,
                                                                          nodeID);

        // computing for rel. attr. the corresponding lattice node
        RelationBuilder ctx = fullRCF
                .getForName(relAttrData.getContextName());
        if (ctx == null)
            System.out
                    .println("Unable to locate working context when reducing relational labeling...");
        Node<Concept> cn = ctx.getLattice().findNode(relAttrData.getNodeID());
        if (cn == null) {
            System.out.println("Scaling concept not found!");
        } else
            relAttrData.setConceptNode(cn);
        return relAttrData;
    }

    /**
     * @param workingRCF
     * @param context
     * @param relAttrsData
     * @return
     */
    private static Vector getConceptMinimas(RelationBuilder context,
                                            Vector relAttrsData) {
        // the following vector is used to store the resulting minimal nodes
        // it is possible to have several minimal when some nodes are not
        // comparable
        Vector minimas = new Vector();
        Sort(relAttrsData);
        while (relAttrsData.size() > 0) {
            RelationalAttributeData minima = (RelationalAttributeData) relAttrsData
                    .elementAt(0);
            relAttrsData.remove(0);
            for (int k = 0; k < relAttrsData.size(); k++) {
                RelationalAttributeData newMinima = (RelationalAttributeData) relAttrsData
                        .elementAt(k);
                if (minima.getRelationName()
                        .compareTo(newMinima.getRelationName()) == 0)
                    // if(newMinima.getConceptNode().getConcept().getIntent().containsAll(minima.getConceptNode().getConcept().getIntent()))
                    // {
                    if (newMinima.getConceptNode().getContent().getExtent()
                            .containsAll(
                                         minima.getConceptNode().getContent()
                                                 .getExtent())) {
                        // minima = newMinima;
                        relAttrsData.remove(k);
                        k = k - 1;
                    }
            }// for
            minimas.add(minima);
        }// while
        return minimas;
    }

    /**
     * @param relAttrsData
     */
    private static void Sort(Vector relAttrsData) {
        // this method sorts the nodes according to ascending size of extent
        for (int i = 0; i < relAttrsData.size() - 1; i++) {
            RelationalAttributeData external = (RelationalAttributeData) relAttrsData
                    .elementAt(i);
            for (int j = i + 1; j < relAttrsData.size(); j++) {
                RelationalAttributeData internal = (RelationalAttributeData) relAttrsData
                        .elementAt(j);
                if (external.getConceptNode().getContent().getExtent().size() > internal
                        .getConceptNode().getContent().getExtent().size()) {
                    relAttrsData.setElementAt(internal, i);
                    relAttrsData.setElementAt(external, j);
                    external = (RelationalAttributeData) relAttrsData
                            .elementAt(i);
                    internal = (RelationalAttributeData) relAttrsData
                            .elementAt(j);
                }
            }// internal
        }// external
    }

    /**
     * @param intent
     * @param links
     * @param minimas
     */
    private static void replace(Intent intent, Vector links, Vector minimas) {
        // System.out.println("content of concept intent before RL reduction");
        // Iterator it=intent.iterator();
        // while(it.hasNext()) System.out.println(it.next().toString());

        Vector intentVector = new Vector(intent);
        for (int i = 0; i < intentVector.size(); i++) {
            FormalAttribute fa = (FormalAttribute) intentVector.elementAt(i);
            if (exists(links, fa))
                intent.remove(fa);
        }
        // adding the links minimas
        for (int i = 0; i < minimas.size(); i++) {
            RelationalAttributeData temp = (RelationalAttributeData) minimas
                    .elementAt(i);
            intent.add(temp.getFormalAttribute());
        }
        // System.out.println("content of concept intent after RL reduction");
        // it=intent.iterator();
        // while(it.hasNext()) System.out.println(it.next().toString());
        return;
    }

    /**
     * @param minimas
     * @param fa
     */
    private static boolean exists(Vector links, FormalAttribute fa) {
        Iterator linksIt = links.iterator();
        while (linksIt.hasNext()) {
            FormalAttribute link = (FormalAttribute) linksIt.next();
            if (link.getName().compareTo(fa.getName()) == 0)
                return true;
        }
        return false;
    }
}
