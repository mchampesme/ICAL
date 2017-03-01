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

package lattice.util.structure;

import java.util.Iterator;
import java.util.List;

import lattice.util.concept.Concept;

/**
 * <p>
 * Titre : Lattice
 * </p>
 * <p>
 * Description : Manipulation des treillis
 * </p>
 * <p>
 * Copyright : Copyright (c) 2002
 * </p>
 * <p>
 * Société : Université de Montréal
 * </p>
 * 
 * @author Alexandre Frantz et Pascal Camarda
 * @version 1.0
 */

/*
 * Title : Réingénierie du package util : Fusion de util et util2 Description :
 * Transfert de la classe ConceptLattice (util) Des méthodes ont été supprimé
 * parce que se trouvant déja dans les classes dont la classe hérite ou
 * deplacees vers d'autres package Copyright: Copyright (c) 2004 Company:
 * Universite de Montréal
 * 
 * @version 1.1 @author Mame Awa Diop et Petko Valtchev TODO To change the
 *          template for this generated type comment go to Window - Preferences -
 *          Java - Code Style - Code Templates
 */
public interface CompleteConceptLattice extends Iterable<Node<Concept>> {

    public void add(Node<Concept> node);

    public void addBottomToIntentLevelIndex(Node<Concept> bottom);

    // Ajout de fusion util et util2
    public Node<Concept> findBottom();

    public Node<Concept> findNode(Integer conceptNodeID);

    // Ajout de fusion util et util2
    public Node<Concept> findTop();

    public Node<Concept> getBottom();

    public Node<Concept> getNode(Concept c);

    // Pour avoir une description
    public String getDescription();

    public List<List<Node<Concept>>> getIntentLevelIndex();

    /**
     * 
     */
    public double getMinSupp();

    public Node<Concept> getTop();

    /**
     * set number of concepts + 1
     */
    public void incNbOfNodes();

    public void initialiseIntentLevelIndex(int size);

    // Ajout de fusion util et util2
    public boolean isEmpty();

    public Iterator<Node<Concept>> iterator();

    public void remove(Node<Concept> concept);

    public void set_max_transaction_size(int m);

    public void setBottom(Node<Concept> buttom);

    public void setDescription(String eDesc);

    /**
     * @param d
     */
    public void setMinSupp(double d);

    /**
     * set of number of concepts
     */
    public void setNbOfNodes(int n);

    // Dans Magalice

    public void setTop(Node<Concept> top);

    // Dans Bordat
    public void setUpperCover(Node<Concept> n1, Node<Concept> n2);

    public int size();
}
