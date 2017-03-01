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

import java.util.ArrayList;

import lattice.alpha.util.Relation;

/**
 * @author Mr ROUME (initial version)
 * @author Marc Champesme (enhanced version)
 * @version 3 janvier 2007
 */
public class RelationalContextFamily extends ArrayList<RelationBuilder> {

    /**
     * 
     */
    private static final long serialVersionUID = 384061879680747581L;

    public static String DEFAULT_NAME = "Default Name";

    // Il est préférable que les contextes soient nommées
    private String name;

    // Gestion des entrees sorties

    /**
     * Constructor for RelationalContext.
     */
    public RelationalContextFamily() {
        name = DEFAULT_NAME;
    }

    /**
     * Constructor for RelationalContext.
     */
    public RelationalContextFamily(String leNom) {
        name = leNom;
    }

    /**
     * Gets the nom.
     * 
     * @return Returns a String
     */
    public String getName() {
        return name;
    }

    /**
     * Sets the name.
     * 
     * @param name
     *            The nom to set
     */
    public void setName(String name) {
        this.name = name;
        if (size() == 1
            && get(0).getName().equals(Relation.DEFAULT_NAME)) {
            get(0).setName(name);
        }
    }

    /**
     * @param sourceCtx
     * @return
     */
    public RelationBuilder getForName(String relName) {
        for (RelationBuilder current : this) {
            if (current.getName().equals(relName))
                return current;
        }
        return null;
    }

    public RelationalContextFamily clone() {
        return (RelationalContextFamily) super.clone();
    }
}
