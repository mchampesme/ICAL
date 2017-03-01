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

import rule.generator.*;
import lattice.util.concept.ConceptImp;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.concept.Intent;
import lattice.util.concept.SetExtent;
import lattice.util.concept.SetIntent;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.structure.CompleteConceptLattice;
import lattice.util.structure.CompleteConceptLatticeImp;
import lattice.util.structure.ConceptNode;
import lattice.util.structure.ConceptNodeImp;

/**
 * <p>Titre : </p>
 * <p>Description : </p>
 * <p>Copyright : Copyright (c) 2004</p>
 * <p>Société : </p>
 * @author not attributable
 * @version 1.0
 */

public class DivideAndConquer {

  public static CompleteConceptLattice constructO(MatrixBinaryRelationBuilder br, int j, int k,
                                          boolean gens) {
    if (Math.abs(k - j) != 0)
      return lattice.algorithm.merge.ObjectMerge.fusionne(constructO(br, j,
          j + Math.abs(k - j) / 2, gens),
                                                constructO(br,
          j + Math.abs(k - j) / 2 + 1, k, gens), br, br, gens);
    else {
      CompleteConceptLattice lat = new CompleteConceptLatticeImp();
      Extent e = new SetExtent();
      Intent i = new SetIntent();
      e.add(br.getFormalObject(j));
    i = br.getIntent(br.getFormalObject(j));
      ConceptImp c = new ConceptImp(e, i);
      ConceptNode topNode = new ConceptNodeImp(c);
      Jen jen = new Jen(br.getLattice());
      jen.calculGenerateursNoeud(topNode);
      lat.setTop(topNode);
      lat.incNbOfNodes();
      lat.initialiseIntentLevelIndex(br.getAttributesNumber() + 1);
      lat.add(topNode);
      int sizeIntent = (c.getIntent()).size();
      int size = br.getAttributesNumber();
      if (size > sizeIntent) {
        ConceptImp bottom = null;
        Intent bottomIntent = new SetIntent();
        Extent bottomExtent = new SetExtent();
        FormalAttribute[] fa = br.getFormalAttributes();
        for (int l = 0; l < size; l++) {
          bottomIntent.add(fa[l]);
        }
        bottom = new ConceptImp(bottomExtent, bottomIntent);
        ConceptNode bottomNode = new ConceptNodeImp(bottom);
        lat.setBottom(bottomNode);
        lat.setUpperCover(topNode, bottomNode);
        lat.add(bottomNode);
        lat.incNbOfNodes();
      }
      else lat.setBottom(topNode);
      return lat;
    }
  }

  public static CompleteConceptLattice constructA(
                                                    MatrixBinaryRelationBuilder br,
                                                    int j, int k) {
        if (Math.abs(k - j) != 0)
            return lattice.algorithm.merge.AttributeMerge
                    .fusionne(constructA(br, j, j + Math.abs(k - j) / 2),
                              constructA(br, j + Math.abs(k - j) / 2 + 1, k),
                              br, br);
        else {
            CompleteConceptLattice lat = new CompleteConceptLatticeImp();
            Extent e = new SetExtent();
            Intent i = new SetIntent();
            i.add(br.getFormalAttribute(j));
            e = br.getExtent(br.getFormalAttribute(j));
            ConceptImp c = new ConceptImp(e, i);
            ConceptNode bottomNode = new ConceptNodeImp(c);
            lat.setBottom(bottomNode);
            lat.incNbOfNodes();
            lat.initialiseIntentLevelIndex(br.getAttributesNumber() + 1);
            lat.add(bottomNode);
            int sizeExtent = (c.getExtent()).size();
            int size = br.getObjectsNumber();
            if (size > sizeExtent) {
                ConceptImp top = null;
                Intent topIntent = new SetIntent();
                Extent topExtent = new SetExtent();
                FormalObject[] fo = br.getFormalObjects();
                for (int l = 0; l < size; l++) {
                    topExtent.add(fo[l]);
                }
                top = new ConceptImp(topExtent, topIntent);
                ConceptNode topNode = new ConceptNodeImp(top);
                lat.setTop(topNode);
                lat.setUpperCover(topNode, bottomNode);
                lat.add(topNode);
                lat.incNbOfNodes();
            } else
                lat.setTop(bottomNode);
            return lat;
        }
    }

}
