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

package rule.util;

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

import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import lattice.util.concept.SetIntent;

public class OnlineGeneratorToolSet {

  public static Intent calculDifference( Intent i1, Intent i2 ) {
    if( i2.size() == 0 ) return (Intent) i1.clone();
    Intent difference = new SetIntent();
    if( i1.size() == 0 ) return difference;
    Iterator i, j;
    i = i1.iterator();
    j = i2.iterator();
    FormalAttribute x = (FormalAttribute) i.next();
    FormalAttribute y = (FormalAttribute) j.next();
    boolean finV1 = false; // finV1 indique si le vecteur v1 a été parcouru
    boolean finV2 = false; // finV2 indique si le vecteur v2 a été parcouru

    // Parcours de la liste des objets du vecteur v1 et du Vecteur v2.
    while( !finV1 && !finV2 ) {
      if ( x == y ) {
        // Les deux vecteurs possèdent l'objet x en commun.
        if ( i.hasNext() ) {
          x = (FormalAttribute) i.next();
        }
        else {
          // Le vecteur V1 a été parcouru.
          finV1 = true;
        }
        if ( j.hasNext() ) {
          y = (FormalAttribute) j.next();
        }
        else {
          // Le vecteur V2 a été parcouru.
          finV2 = true;
        }
      } else {
        if ( x.compareTo(y) < 0 ) {
          difference.add( x );
          if ( i.hasNext() ) {
            x = (FormalAttribute) i.next();
          }
          else {
            // Le vecteur V1 a été parcouru.
            finV1 = true;
          }
        } else {
          if ( j.hasNext() ) {
            y = (FormalAttribute) j.next();
          }
          else {
            // Le vecteur V2 a été parcouru.
            finV2 = true;
          }
        }
      }
    }
    if(!finV1) {
      difference.add( x );
      while ( i.hasNext() ) {
        x = (FormalAttribute) i.next();
        difference.add( x );
      }
     }
    return difference;
  }

  private static int compareVecteurs( Intent i1, Intent i2 ){
  // 0: identique
  // 1: v1 > v2
  // -1: v1 < v2
  if( i1.size() < i2.size() ) return -1;
  if( i1.size() > i2.size() ) return 1;
  if( i1.size() == 0 ) return 0;
  Iterator it1 = i1.iterator();
  Iterator it2 = i2.iterator();
  FormalAttribute a1 = (FormalAttribute) it1.next();
  FormalAttribute a2 = (FormalAttribute) it2.next();
  if (a1.compareTo(a2) < 0) return -1;
  if (a1.compareTo(a2) > 0) return 1;
  return 0;
}


// Partitionne du vecteur rentré en paramètre en deux sous-vecteurs
  private static int partitionCroissant ( Vector vecteur, int inf, int sup ) {

    // Pivot correspond a la taille de l'itemset d'un noeud du vecteur non trié
    Intent noeudPivot =(Intent) vecteur.elementAt( ( inf + sup ) / 2 );
    // int taillePivot = noeudPivot.size();

    int i = inf - 1;
    int j = sup + 1;
    Intent temp = null;

    // Tant que les index ne se croisent pas
    while ( i < j ) {

      // Conserver les noeuds ayant une taille d'itemset inférieure ou égale a la taille pivot
      do {
        i++;
      } while( compareVecteurs((Intent)vecteur.elementAt( i ), noeudPivot) == -1 );
      //while ( ((Vector)vecteur.elementAt( i )).size() < taillePivot  );

      // Conserver les noeuds ayant une taille d'itemset supérieure ou égale a la taille pivot
      do {
        j--;
      } while( compareVecteurs((Intent)vecteur.elementAt( j ), noeudPivot) == 1 );
      //while ( ((Vector)vecteur.elementAt( j )).size() > taillePivot  );

      // Permuter les noeuds qui ne sont pas a leur place
      if ( i < j ) {
        temp = (Intent)vecteur.elementAt( i );
        vecteur.set( i, (Intent)vecteur.elementAt( j ) );
        vecteur.set( j, temp );
      }
    }
    // Indice correspondant a la subdivision dans le vecteur
    return j;
  }

  // Trie suivant les itemsets croissants a partir du partitionnement
  public static void quicksortCroissant ( Vector vecteur, int inf, int sup ) {

    // Itemset délimitant les deux parties du vecteur
    int milieu = 0;

    // S'il y a au moins deux noeuds
    if ( sup > inf ) {
      milieu = partitionCroissant( vecteur, inf, sup );

      // Tri de la partie gauche du vecteur
      quicksortCroissant( vecteur, inf, milieu );

      // Tri de la partie droite du vecteur
      quicksortCroissant( vecteur, milieu + 1, sup );
    }
  }

  // Retourne vrai si le vecteur correspondant a l'itemset du vecteur
  // rentré en paramètre inclut l'itemset du noeud courant
  public static boolean estInclus( Vector v1, Vector v2 ) {

    if( v2  == null || v2 .size() == 0 ) return true;
    if( v1  == null || v1 .size() == 0 ) return false;
    if( v1.size() < v2.size() ) return false;

    // Sélection du premier item de l'itemset du noeud courant et de celui du vecteur rentré en paramètre
    Iterator i = v1 .iterator();
    Iterator j = v2 .iterator();
    int x = ((Integer)i.next()).intValue();
    int y = ((Integer)j.next()).intValue();
    boolean fin = false;

    while( !fin ) {
      // Les deux items sélectionnés sont identiques
      if( x==y ) {
        if( j.hasNext() ) {
          y = ((Integer)j.next()).intValue();
        }
        else {
          return true;
        }
        if( i.hasNext() ) {
          x = ((Integer)i.next()).intValue();
        }
        else {
          return false;
        }
      }
      else {
        // L'item de l'itemset du vecteur rentré en paramètre est inférieur a celui de l'item du noeud courant
        if( x < y ) {
          if( i.hasNext() ) {
            x = ((Integer)i.next()).intValue();
          }
          else {
            return false;
          }
        }
        else {
          return false;
        }
      }
    }
    return true;
  }
}
