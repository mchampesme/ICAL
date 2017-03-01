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

package lattice.util.concept;

/**
 * Titre : Classe des concepts
 * Description :  Renommer la classe Concept(util)
 * Copyright :    Copyright (c) 2004
 * Soci»t» :Universite de MontrÈal
 * @author Mame Awa Diop et Petko Valtchev
 * @version 1.0
 */

import java.util.List;
import java.util.Vector;


public class ConceptImp implements Concept
{	
  private Extent extent;
  private Intent intent;
  private List<Intent> generator;

  /**
   *
   * @param extent
   * @param intent
   */
  public ConceptImp(Extent extent, Intent intent)
  {
    this.extent=extent;
    this.intent=intent;
    this.generator = new Vector<Intent>();
   }

  /**
   *
   * @return extent
   */
  public Extent getExtent()
  {
    return extent;
  }

  /**
   *
   * @return intent
   */

  public Intent getIntent()
  {
    return intent;
  }
  
  /**
   *
   * @return generator
   */

  public List<Intent> getGenerator()
  {
    return generator;
  }

  /**
   *
   * @param extent
   */
  public void setExtent(Extent extent)
  {
    this.extent = extent ;
  }
  
  /**
   *
   * @param generator
   */
  public void setGenerator(List<Intent> generatorsList)
  {
    this.generator = generatorsList ;
  }

  /**
   *
   * @param intent
   */
  public void setIntent(Intent intent)
  {
    this.intent = intent ;
  }

  /**
   * Deux concepts sont »gaux si leurs intents et extents sont »gaux.
   * @param obj
   * @return boolean value
   */
  public boolean equals(Object obj)
  {
    Concept concept_out = (Concept)obj;
    if(extent.equals(concept_out.getExtent()) &&
       intent.equals(concept_out.getIntent()))
      return true;
    else
      return false;
  }

  /**
   * affiche le contenu de l'extent et l'intent d'un concept.
   * @return
   */
  public String toString()
  {
    String string = "";
    string = string.concat("{ ");
    string = string.concat(extent.toString());
    string = string.concat(" , ");
    string = string.concat(intent.toString());
    string = string.concat(" }");
    return string;
  }

}




