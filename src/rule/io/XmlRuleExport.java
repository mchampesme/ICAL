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

package rule.io;

/**************************************************************************/
/* Cette classe permet de sauvegarder l'ensemble des r�gles d'association */
/* approximatives de la base de couverture de Luxemburger dans un fichier */
/* xml.                                                                   */
/***************************************************************************/

import java.io.FileWriter;
import java.io.IOException;
import java.util.Iterator;
import java.util.Set;

import lattice.util.concept.FormalAttribute;
import lattice.util.concept.Intent;
import rule.util.Rule;

public class XmlRuleExport {


   public void sauvegardeReglesExactesFichierXML ( String dbFileName, Set<Rule> ensembleRegles, String nomFichierEntree, double confianceMinimale, double supportMinimal) {
    try {

      FileWriter out = new FileWriter( dbFileName );
      out.write( "<?xml version = '1.0' encoding = 'ISO-8859-1'?>" );

      // DTD
       out.write( "<!DOCTYPE base_couverture SYSTEM 'Rules.dtd'> " );
       // Feuille de style
      out.write( "<?xml-stylesheet type='text/xsl' href='ExactRules.xsl'?>" );

      // Racine du document xml
      out.write( "<base_couverture>" );
      out.write( "<caracteristiques>" );

      out.write( "<base_donnees>" );
      out.write( nomFichierEntree );
      out.write( "</base_donnees>" );

      out.write( "<support_minimal>" );
      String supportUsager = Double.toString( supportMinimal );
      out.write( supportUsager );
      out.write( "</support_minimal>" );

      out.write( "<confiance_minimale>" );
      String confianceUsager = Double.toString( confianceMinimale );
      out.write( confianceUsager);
      out.write( "</confiance_minimale>" );
      out.write( "</caracteristiques>" );

      Iterator<Rule> it = ensembleRegles.iterator();

      out.write( "<ensemble_regles>" );
      out.write( "<nombre_regles>" );
      out.write(new Integer(ensembleRegles.size()).toString() );
      out.write( "</nombre_regles>" );

      while ( it.hasNext()) {

          Rule regleCourante = it.next();
          Intent antecedent = regleCourante.getAntecedent();
          Iterator<FormalAttribute> it2 = antecedent.iterator();
          Intent consequence = regleCourante.getConsequence();
          Iterator<FormalAttribute> it3 = consequence.iterator();

          out.write( "<regle>" );
          out.write( "<antecedent>");
          while ( it2.hasNext() ) {

            // Enregistrement de l'ant�c�dent de la r�gle
            String itemCourantant = it2.next().toString();
            out.write( itemCourantant  );
            out.write(" ");
          }
          out.write( "</antecedent>");

          out.write( "<consequence>" );
          while ( it3.hasNext() ) {

            // Enregistrement de la cons�quence de la r�gle
            String itemCourantcons = it3.next().toString();
            out.write ( itemCourantcons  );
            out.write(" ");
          }
          out.write( "</consequence>" );

          out.write( "<support>" );
          // Enregistrement du support de la r�gle
          String s = Double.toString(((double)((int)(regleCourante.getSupport() * 100.0))) / 100.0 );
          out.write( s );
          out.write( "</support>" );

          out.write( "<confiance>" );

          // Enregistrement de la confiance de la r�gle
          String c = Double.toString(((double)((int)(regleCourante.getConfiance()* 100.0))) / 100.0 );
          out.write( c );
          out.write( "</confiance>" );
          out.write( "</regle>" );
        }
        out.write( "</ensemble_regles>" );
        out.write( "</base_couverture>" );
        out.flush();
        out.close();
      }
      catch( IOException ioe ) {
        System.out.println("Impossible d'enregistrer " + dbFileName);
        ioe.printStackTrace();
      }
    }
    
   public void sauvegardeReglesApproximativesFichierXML ( String dbFileName, Set<Rule> ensembleRegles, String nomFichierEntree, double confianceMinimale, double supportMinimal ) {
    try {

      FileWriter out = new FileWriter( dbFileName );
      out.write( "<?xml version = '1.0' encoding = 'ISO-8859-1'?>" );

      // DTD
      out.write( "<!DOCTYPE base_couverture SYSTEM 'Rules.dtd'> " );

      // Feuille de style
      out.write( "<?xml-stylesheet type='text/xsl' href='ApproxRules.xsl'?>" );

      // Racine du document xml
      out.write( "<base_couverture>" );
      out.write( "<caracteristiques>" );

      out.write( "<base_donnees>" );
      out.write( nomFichierEntree );
      out.write( "</base_donnees>" );

      out.write( "<support_minimal>" );
      String supportUsager = Double.toString( supportMinimal );
      out.write( supportUsager );
      out.write( "</support_minimal>" );

      out.write( "<confiance_minimale>" );
      String confianceUsager = Double.toString( confianceMinimale );
      out.write( confianceUsager);
      out.write( "</confiance_minimale>" );
      out.write( "</caracteristiques>" );

      Iterator<Rule> it = ensembleRegles.iterator();

      out.write( "<ensemble_regles>" );
      out.write( "<nombre_regles>" );
      out.write(new Integer(ensembleRegles.size()).toString() );
      out.write( "</nombre_regles>" );

      while ( it.hasNext()) {

          Rule regleCourante = it.next();
          Intent antecedent = regleCourante.getAntecedent();
          Iterator<FormalAttribute> it2 = antecedent.iterator();
          Intent consequence = regleCourante.getConsequence();
          Iterator<FormalAttribute> it3 = consequence.iterator();

          out.write( "<regle>" );
          out.write( "<antecedent>");
          while ( it2.hasNext() ) {

            // Enregistrement de l'ant�c�dent de la r�gle
            String itemCourantant = it2.next().toString();
            out.write( itemCourantant  );
            out.write(" ");
          }
          out.write( "</antecedent>");

          out.write( "<consequence>" );
          while ( it3.hasNext() ) {

            // Enregistrement de la cons�quence de la r�gle
            String itemCourantcons = it3.next().toString();
            out.write ( itemCourantcons  );
            out.write(" ");
          }
          out.write( "</consequence>" );

          out.write( "<support>" );
          // Enregistrement du support de la r�gle
          String s = Double.toString(((double)((int)(regleCourante.getSupport() * 100.0))) / 100.0 );
          out.write( s );
          out.write( "</support>" );

          out.write( "<confiance>" );

          // Enregistrement de la confiance de la r�gle
          String c = Double.toString(((double)((int)(regleCourante.getConfiance()* 100.0))) / 100.0 );
          out.write( c );
          out.write( "</confiance>" );
          out.write( "</regle>" );
        }
        out.write( "</ensemble_regles>" );
        out.write( "</base_couverture>" );
        out.flush();
        out.close();
      }
      catch( IOException ioe ) {
        System.out.println("Impossible d'enregistrer " + dbFileName);
        ioe.printStackTrace();
      }
    }
}