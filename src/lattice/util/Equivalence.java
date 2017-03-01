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

package lattice.util;

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import lattice.util.concept.Concept;
import lattice.util.concept.Intent;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.Node;

/**
 * @author Kamal Nehme To change this generated comment edit the template
 *         variable "typecomment": Window>Preferences>Java>Templates. To enable
 *         and disable the creation of type comments go to
 *         Window>Preferences>Java>Code Generation.
 */
public class Equivalence {

    Node<Concept> node;

    Vector Eq;

    public Equivalence() {
        node = null;
        Eq = new Vector();
    }

    public Equivalence(Node<Concept> firstNode) {
        node = firstNode;
        Eq = new Vector();
    }

    public Node<Concept> getMinimal() {
        return this.node;
    }

    public void setMinimal(Node<Concept> min) {
        this.node = min;
    }

    public Vector getGen() {
        return Eq;
    }

    public void updateGen(List list) {
        // System.out.println("Gen: "+v);
        for (int i = 0; i < list.size(); i++) {
            Intent intent = (Intent) list.get(i);
            // System.out.println(">>>> Execution of GEN: "+intent);
            if (intent.isEmpty())
                Eq.add(0, intent);

            // if (!intent.isEmpty()){
            else {
                boolean reductible = isReductible(intent);
                // System.out.println(" "+intent+" REDUCTIBLE: "+reductible);
                if (!reductible) {
                    boolean fin = false;
                    int k = 0;
                    Iterator itEq = Eq.iterator();
                    while (itEq.hasNext() && !fin) {
                        if (intent.size() > ((Intent) itEq.next()).size())
                            k++;
                        else
                            fin = true;
                    }
                    Eq.add(k, intent);
                }
            }

        }
    }

    public boolean isReductible(Intent intent) {
        Iterator itr = Eq.iterator();
        boolean fini = false;
        boolean fin = false;

        while ((itr.hasNext()) && (!fin)) {
            Intent itrNext = (Intent) itr.next();
            if (intent.containsAll(itrNext)) {
                fini = true;
                fin = true;
            }
            if (itrNext.size() > intent.size())
                fin = true;
        }
        return fini;
    }

}
