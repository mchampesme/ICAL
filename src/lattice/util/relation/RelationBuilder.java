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

package lattice.util.relation;

import java.util.List;

import lattice.alpha.util.Relation;
import lattice.util.concept.AbstractFormalAttributeValue;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.exception.BadInputDataException;
import lattice.util.structure.CompleteConceptLattice;

/**
 * @author Mr ROUME (AbstractRelation)
 * @author Marc Champesme
 */
public interface RelationBuilder extends Relation, Cloneable {

    public void addObject();

    public void addObject(FormalObject fo);

    public void removeObject(FormalObject fo);

    public void addAttribute();

    public void addAttribute(FormalAttribute fa);

    public void removeAttribute(FormalAttribute fa);

    public FormalObject getFormalObject(int idxO);

    public List<FormalObject> getObjects();

    public FormalObject[] getFormalObjects();

    public FormalAttribute getFormalAttribute(int idxA)
                                                       throws BadInputDataException;

    public FormalObject getObjectForName(String objectName);

    public FormalAttribute getAttributeForName(String attributeName);

    public List<FormalAttribute> getAttributes();

    public FormalAttribute[] getFormalAttributes();

    public void replaceAttribute(FormalAttribute prevName,
                                 FormalAttribute newName)
                                                         throws BadInputDataException;

    public void replaceAttribute(int idxA, FormalAttribute newName)
                                                                   throws BadInputDataException;

    public void replaceObject(FormalObject prevName, FormalObject newName)
                                                                          throws BadInputDataException;

    public void replaceObject(int idxO, FormalObject newName)
                                                             throws BadInputDataException;

    public AbstractFormalAttributeValue getRelation(FormalObject Obj,
                                                    FormalAttribute Att);

    public AbstractFormalAttributeValue getRelation(int idxO, int idxA);

    public void setRelation(FormalObject Obj, FormalAttribute Att,
                            AbstractFormalAttributeValue rel)
                                                             throws BadInputDataException;

    public void setName(String nom);

    public void setLattice(CompleteConceptLattice cl);

    public boolean containsObjectForName(String objectName);

    public RelationBuilder clone();

    public void emptyRelation();

}