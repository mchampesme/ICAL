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

package rule.generator;

/**
 * <p>Titre : Petko&al 2</p>
 * <p>Description : PetkoInc (plate forme)</p>
 * <p>Copyright : Copyright (c) 2003</p>
 * <p>Société : UQAM - UdM</p>
 * @author Céline Frambourg
 * @version 2.0
 */

import java.util.Vector;
import java.util.Iterator;

import lattice.util.concept.ConceptImp;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import lattice.util.concept.SetIntent;
import rule.util.OnlineGeneratorToolSet;

public class ValtchevAlOnlineGeneratorUpdate {

  // METHODES D'INSTANCE

  private static boolean inclusion ( Intent g, Intent intentConcept ) {
    boolean reponse = false;
    if ( intentConcept.containsAll(g)) {
      reponse = true;
    }
    return reponse;
  }

  private static boolean inclusion ( Vector g, Vector intentConcept ) {
    boolean reponse = false;
    if ( OnlineGeneratorToolSet.estInclus( intentConcept, g )) {
      reponse = true;
    }
    return reponse;
  }

  private static void modificationOldGenerators( ConceptImp c, ConceptImp cBarre) {
    Iterator it = c.getGenerator().iterator();
    Vector temp = new Vector();
    while ( it.hasNext() ) {
      Intent g = (Intent) it.next();
      if (inclusion( g, cBarre.getIntent()) == true ) {
        cBarre.getGenerator().add( g );
        temp.add( g );
      }
    }
    c.getGenerator().removeAll( temp );
  }

  private static void modificationNewGenerators( ConceptImp c, ConceptImp cBarre) {
    Iterator it1 = cBarre.getGenerator().iterator();
    while ( it1.hasNext()) {
      Intent gBarre = (Intent) it1.next();
      Vector newGens = new Vector();
      Intent faceCourante = calculFace(c, cBarre);
      Iterator it2 = faceCourante.iterator();
      while ( it2.hasNext()) {
        Intent gUnionA = new SetIntent();
        boolean genCond = true;
        FormalAttribute a = ( FormalAttribute ) it2.next();
        gUnionA = (Intent)gBarre.clone();
        gUnionA.add( a );

        Iterator it3= c.getGenerator().iterator();
        while ( it3.hasNext()) {
          Intent g = (Intent) it3.next();
          if (inclusion( g, gUnionA)) {
            genCond = false;
          }
        }
        if ( genCond == true ) {
          newGens.add( gUnionA );
          c.getGenerator().add( gUnionA );
        }
      }
    }
  }

  // Calcul la face de deux concepts
  private static Intent calculFace( ConceptImp c, ConceptImp cBarre ) {
    return  OnlineGeneratorToolSet.calculDifference( c.getIntent(), cBarre.getIntent() );
  }

  public static void computeGenerators( ConceptImp c, ConceptImp cBarre ) {
    modificationOldGenerators( c, cBarre );
    if (!(cBarre.getGenerator() instanceof Vector))
        cBarre.setGenerator(new Vector(cBarre.getGenerator()));
    sort( (Vector) cBarre.getGenerator() );
    modificationNewGenerators( c, cBarre );
  }


  private static void sort( Vector generators ) {
    int tailleMax = generators.size()-1;
    OnlineGeneratorToolSet.quicksortCroissant( generators, 0, tailleMax );
  }
}