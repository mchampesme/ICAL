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

package lattice.gui.graph.magneto;

import java.util.Vector;

/**
 * <p>Title: Galicia</p>
 * <p>Description: Galois Lattice Interactive Constructor</p>
 * <p>Copyright: Copyright (c) 2002</p>
 * <p>Company: University of Montreal</p>
 * @author David Grosser
 * @version 1.0
 */

/**********************************
* Classe abstraite des effecteurs *
***********************************/
  public abstract class ActionObject {

    protected Vector magnetables; // Les noeuds magnétiques
    protected int level;
    protected int nbNiveau;
    protected Magneto magneto;
    protected int x = 0;
    protected int y = 0;
    protected int nbMagnetables;

    public ActionObject(Magneto magneto, int level, int nbNiveau) {
      this.magneto = magneto;
      this.level = level;
      this.nbNiveau = nbNiveau;
    }

    /**
     * Démarrage d'une action
     */
    protected abstract boolean doAction(boolean threeDMode);

    //protected abstract boolean doActionX();

    //protected abstract boolean doActionZ();

    public void fix(boolean b) {
      for(int i=0; i<nbMagnetables; i++) getMagnetable(i).setIsMagnetable(! b);
    }

// Retourner le ième élément magnétique
  Magnetable getMagnetable(int i) {
    return (Magnetable) magnetables.elementAt(i);
  }

    protected void setMousePosition(int x, int y) {
      this.x = x; this.y = y;
    }
    /**
     * Pour ne pas agir sur certains niveaux
     */
    protected boolean isFixedLevel() {
      if(level == 0) return true;
      if(magneto.fixFirstLevel() && (level == 1)) return true;
      if(magneto.fixLastLevel() && (level == nbNiveau-2)) return true;
      if(level == nbNiveau-1) return true;
      return false;
    }
  }