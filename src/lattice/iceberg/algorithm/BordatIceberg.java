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

package lattice.iceberg.algorithm;

import java.util.Collection;
import java.util.Date;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.StringTokenizer;
import java.util.Vector;

import lattice.algorithm.LatticeAlgorithm;
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
import lattice.util.structure.Node;

/**
 * @author zuojin To change this generated comment edit the template variable
 *         "typecomment": Window>Preferences>Java>Templates. To enable and
 *         disable the creation of type comments go to
 *         Window>Preferences>Java>Code Generation.
 */

public class BordatIceberg extends LatticeAlgorithm {

    /**
     * @
     */

    protected Vector col;

    protected int nbrAttrs;

    protected int nbrObjs;

    protected double minSupp;

    protected Concept bottom;

    protected Hashtable objs;

    public BordatIceberg(MatrixBinaryRelationBuilder br, double minSupp) {

        super(br);

        // begin Amine
        ConceptNodeImp.resetNodeId();
        // end Amine

        Date date = new Date();

        System.out.println("Begin object construction from " + date.toString());

        this.minSupp = minSupp;
        nbrAttrs = br.getAttributesNumber();

        nbrObjs = br.getObjectsNumber();

        ConceptImp topConcept = null;

        ConceptImp bottomConcept = null;

        col = (Vector) br.getInitialObjectPreConcept(MatrixBinaryRelationBuilder.NO_SORT);
        System.out.println("Begin col " + col);
        objs = new Hashtable(nbrObjs);

        int size = col.size();

        for (int i = 0; i < size; i++) {

            objs.put(((FormalObject) (((ConceptImp) col.get(i)).getExtent())
                    .first()).getName(), new Integer(i));

        }

        topConcept = findTopConcept(col);

        bottom = findBottomConcept(br);

        getLattice().setTop(new ConceptNodeImp(topConcept));
        getLattice().incNbOfNodes();
        getLattice().setBottom(new ConceptNodeImp(bottomConcept));
        getLattice().incNbOfNodes();
        getLattice().initialiseIntentLevelIndex(br.getAttributesNumber() + 1);

        date = new Date();

        System.out.println("End object construction from " + date.toString());

    }

    public BordatIceberg(MatrixBinaryRelationBuilder br) {
        this(br, 0.0d);
    }

    public void doAlgorithm() {

        // jobObserv.sendMessage("Bordat Algorithm is in progress!\n");
        Node<Concept> top = getLattice().getTop();

        doBordat(top);

        // jobObserv.jobEnd(true);

    }

    public String getDescription() {

        return "Bordat incremental iceberg update";

    }

    public ConceptImp findTopConcept(Collection col) {

        ConceptImp top = null;

        Intent topIntent = new SetIntent();

        Extent topExtent = new SetExtent();

        Iterator iter = col.iterator();

        if (iter.hasNext()) {

            ConceptImp first = (ConceptImp) iter.next();

            topIntent = first.getIntent();

            topExtent = first.getExtent();

        }

        while (iter.hasNext()) {

            ConceptImp next = (ConceptImp) iter.next();

            topIntent = next.getIntent().intentIntersection(topIntent);

            topExtent = next.getExtent().extentUnion(topExtent);

        }

        top = new ConceptImp(topExtent, topIntent);

        return top;

    }

    public ConceptImp findBottomConcept(MatrixBinaryRelationBuilder br) {

        ConceptImp bottom = null;

        Intent bottomIntent = new SetIntent();

        Extent bottomExtent = new SetExtent();

        FormalAttribute[] fa = br.getFormalAttributes();

        int size = fa.length;

        for (int i = 0; i < size; i++) {

            bottomIntent.add(fa[i]);

        }

        bottom = new ConceptImp(bottomExtent, bottomIntent);

        return bottom;

    }

    public void doBordat(Node<Concept> top) {

        process(top);

        // getLattice().setBottom(getLattice().findBottom());

    }

    public Concept getTop() {

        Concept top = null;

        top = (Concept) getLattice().getTop().getContent();

        return top;

    }

    // public void setTop(ConceptImp top){

    // lcl.setTop(new LatticeNode(top));

    // }

    public void process(Node<Concept> node) {

        ConceptImp concept = (ConceptImp) node.getContent();

        Intent intent = concept.getIntent();

        LinkedList candidate = new LinkedList();

        Hashtable nodeHash = new Hashtable();

        nodeHash.put(concept.toString(), node);

        candidate.addLast(node);

        long nodeProcessed = 0;

        Date date;

        int j = 1;

        date = new Date();

        System.out.println("Begin Calculation from " + date.toString());

        do {

            nodeProcessed++;

            if (nodeProcessed == 1000 * j) {

                date = new Date();

                System.out.println("Process the " + nodeProcessed
                                   + "th node at " + date.toString());

                j++;

            }

            node = (Node<Concept>) candidate.getFirst();

            concept = (ConceptImp) node.getContent();

            Vector lowerCoverFirst = findLowerCover(concept.getExtent(),
                                                    concept.getIntent());
            System.out.println("lowerCocept" + "" + nodeProcessed + ""
                               + lowerCoverFirst);
            int size = lowerCoverFirst.size();

            for (int i = 0; i < size; i++) {

                ConceptImp lowerConcept = (ConceptImp) lowerCoverFirst.get(i);

                if (((lowerConcept.getExtent().size()) / (double) this.nbrObjs) < this.minSupp)
                    continue;

                Node<Concept> childNode;

                if ((childNode = (Node<Concept>) nodeHash.get(lowerConcept
                        .toString())) == null) {

                    childNode = new ConceptNodeImp(lowerConcept);

                    nodeHash.put(lowerConcept.toString(), childNode);

                    candidate.addLast(childNode);
                    System.out.print(nodeProcessed + "" + "[");
                    for (int g = 0; g < candidate.size(); g++) {
                        ConceptImp imp = (ConceptImp) ((Node<Concept>) candidate
                                .get(i)).getContent();
                        System.out.print("candidate" + "   " + imp);
                    }
                    System.out.println("]");
                    getLattice().incNbOfNodes();

                }

                getLattice().setUpperCover(node, childNode);

            }

            getLattice().add(node);

            candidate.removeFirst();

        } while (candidate.isEmpty() == false);

        date = new Date();

        System.out.println("The " + nodeProcessed
                           + "th node is the last one, it was processed at "
                           + date.toString());

    }

    protected Vector findLowerCover(Extent extent, Intent intent) {

        Vector lowerCover = new Vector();

        Intent allAttrs, objIntent, nextObjIntent;

        Extent objExtent;

        ConceptImp nextObj;

        ConceptImp firstObj;

        allAttrs = (Intent) intent.clone();

        Iterator it = extent.iterator();

        while ((firstObj = findFirstObj(allAttrs, it)) != null) {

            objIntent = (Intent) firstObj.getIntent();

            objExtent = (Extent) firstObj.getExtent();

            while (it.hasNext()) {

                nextObj = (ConceptImp) (nextObj(it));

                if (!(allAttrs.containsAll(nextObj.getIntent()
                        .intentIntersection(objIntent)))) {

                    objExtent = objExtent.extentUnion(nextObj.getExtent());

                    objIntent = objIntent.intentIntersection(nextObj
                            .getIntent());

                }

            }

            if (objIntent.intentIntersection(allAttrs).equals(intent)) {

                lowerCover.add(new ConceptImp(objExtent, objIntent));

            }

            allAttrs = allAttrs.intentUnion(objIntent);

            it = extent.iterator();

        }

        // Here we need add the bottom Node of the lattice!!!!!!!!!!!!!!!!!

        if ((lowerCover.size() == 0) && (intent.size() != nbrAttrs)) {

            // lowerCover.add(getLattice().getBottom().getConcept());

            lowerCover.add(this.bottom);
        }

        return lowerCover;

    }

    protected ConceptImp findFirstObj(Intent intent, Iterator it) {

        ConceptImp first = null;

        ConceptImp firstConcept = null;

        FormalObject next;

        while (it.hasNext()) {

            next = (FormalObject) it.next();

            String name = next.getName();

            int nobj = ((Integer) (objs.get(name))).intValue();

            firstConcept = (ConceptImp) col.elementAt(nobj);

            if (!intent.containsAll(firstConcept.getIntent())) {

                break;

            }

            firstConcept = null;

        }

        if (firstConcept != null) {

            first = new ConceptImp((Extent) firstConcept.getExtent().clone(),

            (Intent) firstConcept.getIntent().clone());

        }

        return first;

    }

    protected ConceptImp nextObj(Iterator it) {

        ConceptImp next = new ConceptImp(new SetExtent(), new SetIntent());

        ConceptImp nextConcept = null;

        FormalObject nextObj;

        if (it.hasNext()) {

            nextObj = (FormalObject) it.next();

            String name = nextObj.getName();

            int nobj = ((Integer) (objs.get(name))).intValue();

            nextConcept = (ConceptImp) col.elementAt(nobj);

            next.setExtent((Extent) nextConcept.getExtent().clone());

            next.setIntent((Intent) nextConcept.getIntent().clone());

        }

        return next;

    }

    protected ConceptImp findFirstObj1(Intent intent, Iterator it) {

        // ConceptImp first=new ConceptImp(new SetExtent(),new SetIntent());

        ConceptImp first = null;

        ConceptImp firstConcept = null;

        FormalObject next;

        while (it.hasNext()) {

            next = (FormalObject) it.next();

            String name = next.getName();

            StringTokenizer st = new StringTokenizer(name, "_");

            String noObj = "";

            int nobj = -1;

            while (st.hasMoreTokens()) {

                noObj = st.nextToken();

            }

            try {

                nobj = Integer.parseInt(noObj);

            }

            catch (NumberFormatException e) {

            }

            firstConcept = (ConceptImp) col.elementAt(nobj);

            if (!intent.containsAll(firstConcept.getIntent())) {

                break;

            }

            firstConcept = null;

        }

        if (firstConcept != null) {

            // first.setExtent((Extent)firstConcept.getExtent().clone());

            // first.setIntent((Intent)firstConcept.getIntent().clone());

            first = new ConceptImp((Extent) firstConcept.getExtent().clone(),

            (Intent) firstConcept.getIntent().clone());

        }

        return first;

    }

    protected ConceptImp nextObj1(Iterator it) {

        ConceptImp next = new ConceptImp(new SetExtent(), new SetIntent());

        ConceptImp nextConcept = null;

        FormalObject nextObj;

        if (it.hasNext()) {

            nextObj = (FormalObject) it.next();

            String name = nextObj.getName();

            StringTokenizer st = new StringTokenizer(name, "_");

            String noObj = "";

            int nobj = -1;

            while (st.hasMoreTokens()) {

                noObj = st.nextToken();

            }

            try {

                nobj = Integer.parseInt(noObj);

            }

            catch (NumberFormatException e) {

            }

            nextConcept = (ConceptImp) col.elementAt(nobj);

            next.setExtent((Extent) nextConcept.getExtent().clone());

            next.setIntent((Intent) nextConcept.getIntent().clone());

        }

        return next;

    }
}
