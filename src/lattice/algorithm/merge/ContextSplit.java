/*
 ***********************************************************************
 * Copyright (C) 2004 The Galicia Team 
 *
 * Modifications to the initial code base are copyright of their
 * respective authors, or their employers as appropriate.  Authorship
 * of the modifications may be determined from the ChangeLog placed at
 * the end of this file.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
 * USA; or visit the following url:
 * http://www.gnu.org/copyleft/lesser.html
 *
 ***********************************************************************
 */

package lattice.algorithm.merge;

import java.util.List;
import java.util.Vector;

import lattice.algorithm.LatticeAlgorithmInc;
import lattice.gui.RelationalContextEditor;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLattice;
import lattice.algorithm.ValtchevEtAl2;
import lattice.util.concept.*;
/**
 * <p>Titre : </p>
 * <p>Description : </p>
 * <p>Copyright : Copyright (c) 2004</p>
 * <p>Société : </p>
 * @author not attributable
 * @version 1.0
 */

public class ContextSplit {

  public static Object[][] cutO(RelationalContextEditor rce, MatrixBinaryRelationBuilder br,
                                boolean gens) {
    Object[][] ls = new Object[2][2];
    MatrixBinaryRelationBuilder br1 = new MatrixBinaryRelationBuilder(br.getObjectsNumber() / 2,
                                            br.getAttributesNumber());
    br1.setName(br.getName() + " 1 - " +
                        br.getObjectsNumber() / 2);
    for (int i = 0; i < br1.getAttributesNumber(); i++) {
      try {
        br1.replaceAttribute(i,
                             (FormalAttribute) br.getAttributes().
                             get(i));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br1.getObjectsNumber(); i++) {
      try {
        br1.replaceObject(i,
                          (FormalObject) br.getObjects().
                          get(i));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br1.getObjectsNumber(); i++) {
      for (int j = 0; j < br1.getAttributesNumber(); j++) {
        try {
          br1.setRelation( (FormalObject) br1.getObjects().
                          get(i), (FormalAttribute) br1.getAttributes().
                          get(j), br.getRelation(i, j));
        }
        catch (BadInputDataException ex) {
        }
      }
    }
    rce.addBinaryRelation(br1);
    ls[0][1] = br1;
    LatticeAlgorithmInc algo = new ValtchevEtAl2(br1, gens);
    algo.doAlgorithm();
    ls[0][0] = algo.getLattice();
    ( (CompleteConceptLattice) ls[0][0]).setDescription(br1.getName());
    MatrixBinaryRelationBuilder br2 = new MatrixBinaryRelationBuilder( (br.getObjectsNumber() -
                                              br.getObjectsNumber() / 2),
                                            br.getAttributesNumber());
    br2.setName(br.getName() + " " +
                        (br.getObjectsNumber() / 2 + 1) + " - " +
                        br.getObjectsNumber());
    for (int i = 0; i < br2.getAttributesNumber(); i++) {
      try {
        br2.replaceAttribute(i,
                             (FormalAttribute) br.getAttributes().
                             get(i));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br2.getObjectsNumber(); i++) {
      try {
        br2.replaceObject(i,
                          (FormalObject) br.getObjects().
                          get(i + br1.getObjectsNumber()));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br2.getObjectsNumber(); i++) {
      for (int j = 0; j < br2.getAttributesNumber(); j++) {
        try {
          br2.setRelation( (FormalObject) br2.getObjects().
                          get(i), (FormalAttribute) br2.getAttributes().
                          get(j),
                          br.getRelation(i + br1.getObjectsNumber(), j));
        }
        catch (BadInputDataException ex) {
        }
      }
    }

    ls[1][1] = br2;
    algo = new ValtchevEtAl2(br2, gens);
    algo.doAlgorithm();
    ls[1][0] = algo.getLattice();
    ( (CompleteConceptLattice) ls[1][0]).setDescription(br2.getName());
    rce.addBinaryRelation(br2);
    return ls;
  }

  public static Object[][] cutO(RelationalContextEditor rce, MatrixBinaryRelationBuilder br,
                                Vector o,
                                boolean gens) {
    Object[][] ls = new Object[2][2];
    MatrixBinaryRelationBuilder br1 = new MatrixBinaryRelationBuilder(o.size(),
                                            br.getAttributesNumber());
    br1.setName(br.getName() + " (OBJ : 1 - " +
                        o.size() + ")");
    for (int i = 0; i < br1.getAttributesNumber(); i++) {
      try {
        br1.replaceAttribute(i,
                             (FormalAttribute) br.getAttributes().
                             get(i));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br1.getObjectsNumber(); i++) {
      try {
        br1.replaceObject(i,
                          (FormalObject) o.
                          elementAt(i));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br1.getObjectsNumber(); i++) {
      for (int j = 0; j < br1.getAttributesNumber(); j++) {
        try {
          br1.setRelation( (FormalObject) o.
                          get(i), (FormalAttribute) br1.getAttributes().
                          get(j), br.getRelation( (FormalObject) o.
              get(i), (FormalAttribute) br1.getAttributes().
              get(j)));
        }
        catch (BadInputDataException ex) {
        }
      }
    }
    rce.addBinaryRelation(br1);
    ls[0][1] = br1;
    LatticeAlgorithmInc algo = new ValtchevEtAl2(br1, gens);
    algo.doAlgorithm();
    ls[0][0] = algo.getLattice();
    ( (CompleteConceptLattice) ls[0][0]).setDescription(br1.getName());
    List<FormalObject> temp = new Vector<FormalObject>(br.getObjects());
    temp.removeAll(o);
    MatrixBinaryRelationBuilder br2 = new MatrixBinaryRelationBuilder( (br.getObjectsNumber() -
                                              o.size()),
                                            br.getAttributesNumber());
    br2.setName(br.getName() + " (OBJ : " +
                        (o.size() + 1) + " - " +
                        br.getObjectsNumber() + ")");
    for (int i = 0; i < br2.getAttributesNumber(); i++) {
      try {
        br2.replaceAttribute(i,
                             (FormalAttribute) br.getAttributes().
                             get(i));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br2.getObjectsNumber(); i++) {
      try {
        br2.replaceObject(i,
                          (FormalObject) temp.
                          get(i));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br2.getObjectsNumber(); i++) {
      for (int j = 0; j < br2.getAttributesNumber(); j++) {
        try {
          br2.setRelation( (FormalObject) temp.
                          get(i), (FormalAttribute) br2.getAttributes().
                          get(j), br.getRelation( (FormalObject) temp.
              get(i), (FormalAttribute) br2.getAttributes().
              get(j)));

        }
        catch (BadInputDataException ex) {
        }
      }
    }

    ls[1][1] = br2;
    algo = new ValtchevEtAl2(br2, gens);
    algo.doAlgorithm();
    ls[1][0] = algo.getLattice();
    ( (CompleteConceptLattice) ls[1][0]).setDescription(br2.getName());
    rce.addBinaryRelation(br2);
    return ls;
  }

  public static Object[][] cutA(RelationalContextEditor rce, MatrixBinaryRelationBuilder br) {
    Object[][] ls = new Object[2][2];
    MatrixBinaryRelationBuilder br1 = new MatrixBinaryRelationBuilder(br.getObjectsNumber(),
                                            br.getAttributesNumber() / 2);
    br1.setName(br.getName() + "ATT : 1 - " +
                        br.getAttributesNumber() / 2);
    for (int i = 0; i < br1.getAttributesNumber(); i++) {
      try {
        br1.replaceAttribute(i,
                             (FormalAttribute) br.getAttributes().
                             get(i));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br1.getObjectsNumber(); i++) {
      try {
        br1.replaceObject(i,
                          (FormalObject) br.getObjects().
                          get(i));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br1.getObjectsNumber(); i++) {
      for (int j = 0; j < br1.getAttributesNumber(); j++) {
        try {
          br1.setRelation( (FormalObject) br1.getObjects().
                          get(i), (FormalAttribute) br1.getAttributes().
                          get(j), br.getRelation(i, j));
        }
        catch (BadInputDataException ex) {
        }
      }
    }
    rce.addBinaryRelation(br1);
    ls[0][1] = br1;
    LatticeAlgorithmInc algo = new ValtchevEtAl2(br1);
    algo.doAlgorithm();
    ls[0][0] = algo.getLattice();
    ( (CompleteConceptLattice) ls[0][0]).setDescription(br1.getName());
    MatrixBinaryRelationBuilder br2 = new MatrixBinaryRelationBuilder(br.getObjectsNumber(),
                                            (br.getAttributesNumber() -
                                             br.getAttributesNumber() / 2));
    br2.setName(br.getName() + "ATT : " +
                        (br.getAttributesNumber() / 2 + 1) + " - " +
                        br.getAttributesNumber());
    for (int i = 0; i < br2.getAttributesNumber(); i++) {
      try {
        br2.replaceAttribute(i,
                             (FormalAttribute) br.getAttributes().
                             get(i + br1.getAttributesNumber()));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br2.getObjectsNumber(); i++) {
      try {
        br2.replaceObject(i,
                          (FormalObject) br.getObjects().
                          get(i));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br2.getObjectsNumber(); i++) {
      for (int j = 0; j < br2.getAttributesNumber(); j++) {
        try {
          br2.setRelation( (FormalObject) br2.getObjects().
                          get(i), (FormalAttribute) br2.getAttributes().
                          get(j),
                          br.getRelation(i, j + br1.getAttributesNumber()));
        }
        catch (BadInputDataException ex) {
        }
      }
    }
    ls[1][1] = br2;
    algo = new ValtchevEtAl2(br2);
    algo.doAlgorithm();
    ls[1][0] = algo.getLattice();
    ( (CompleteConceptLattice) ls[1][0]).setDescription(br2.getName());
    rce.addBinaryRelation(br2);
    return ls;
  }

  public static Object[][] cutA(RelationalContextEditor rce, MatrixBinaryRelationBuilder br,
                                Vector a) {
    Object[][] ls = new Object[2][2];
    MatrixBinaryRelationBuilder br1 = new MatrixBinaryRelationBuilder(br.getObjectsNumber(),
                                            a.size());
    br1.setName(br.getName() + " (ATT : 1 - " +
                        a.size() + ")");
    for (int i = 0; i < br1.getAttributesNumber(); i++) {
      try {
        br1.replaceAttribute(i,
                             (FormalAttribute) a.
                             elementAt(i));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br1.getObjectsNumber(); i++) {
      try {
        br1.replaceObject(i,
                          (FormalObject) br.getObjects().
                          get(i));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br1.getObjectsNumber(); i++) {
      for (int j = 0; j < br1.getAttributesNumber(); j++) {
        try {
          br1.setRelation( (FormalObject) br1.getObjects().
                          get(i), (FormalAttribute) a.
                          get(j),
                          br.getRelation( (FormalObject) br1.getObjects().
                                         get(i), (FormalAttribute) a.
                                         get(j)));
        }
        catch (BadInputDataException ex) {
        }
      }
    }
    rce.addBinaryRelation(br1);
    ls[0][1] = br1;
    LatticeAlgorithmInc algo = new ValtchevEtAl2(br1);
    algo.doAlgorithm();
    ls[0][0] = algo.getLattice();
    ( (CompleteConceptLattice) ls[0][0]).setDescription(br1.getName());
    List<FormalAttribute> temp = new Vector<FormalAttribute>(br.getAttributes());
    temp.removeAll(a);
    MatrixBinaryRelationBuilder br2 = new MatrixBinaryRelationBuilder(br.getObjectsNumber(),
                                            (br.getAttributesNumber() - a.size()));
    br2.setName(br.getName() + " (ATT : " +
                        (a.size() + 1) + " - " +
                        br.getAttributesNumber() + ")");
    for (int i = 0; i < br2.getAttributesNumber(); i++) {
      try {
        br2.replaceAttribute(i,
                             (FormalAttribute) temp.
                             get(i));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br2.getObjectsNumber(); i++) {
      try {
        br2.replaceObject(i,
                          (FormalObject) br.getObjects().
                          get(i));
      }
      catch (BadInputDataException ex) {
      }
    }
    for (int i = 0; i < br2.getObjectsNumber(); i++) {
      for (int j = 0; j < br2.getAttributesNumber(); j++) {
        try {
          br2.setRelation( (FormalObject) br2.getObjects().
                          get(i), (FormalAttribute) temp.
                          get(j),
                          br.getRelation( (FormalObject) br2.getObjects().
                                         get(i), (FormalAttribute) temp.
                                         get(j)));

        }
        catch (BadInputDataException ex) {
        }
      }
    }

    ls[1][1] = br2;
    algo = new ValtchevEtAl2(br2);
    algo.doAlgorithm();
    ls[1][0] = algo.getLattice();
    ( (CompleteConceptLattice) ls[1][0]).setDescription(br2.getName());
    rce.addBinaryRelation(br2);
    return ls;
  }

 





}
