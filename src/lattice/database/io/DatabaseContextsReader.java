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

/*
 * Created on 2004-06-21
 * @author Manuel Aupetit
 */
package lattice.database.io;

import java.io.IOException;
import java.util.Vector;

import lattice.database.util.DatabaseConnection;
import lattice.database.util.DatabaseFunctions;
import lattice.database.util.DatabaseManagement;
import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.relation.ScalingBinaryRelation;

/**
 * A class to create a contexts database reader
 * 
 * @author Manuel Aupetit
 */
public class DatabaseContextsReader extends DatabaseAbstractReader {

    private DatabaseManagement dbm;

    private Vector relations;

    public DatabaseContextsReader(DatabaseManagement dbm, Vector relations) {
        this(dbm, relations, DatabaseConnection.getFamilyName());
    }

    public DatabaseContextsReader(DatabaseManagement dbm, Vector relations,
                                  String ctxName) {
        this.dbm = dbm;
        this.relations = relations;
        this.defaultNameForData = ctxName;
    }

    /**
     * @throws BadInputDataException
     * @throws IOException
     */
    public RelationalContextFamily readRelationalContext()
                                                          throws BadInputDataException,
                                                          IOException {

        RelationalContextFamily relCtxFam = new RelationalContextFamily(
                                                                        getDefaultNameForData());

        for (int i = 0; i < relations.size(); i++) {
            String relName = (String) relations.get(i);
            String type = dbm.getRelationType(relName);
            if (type.equals(DatabaseFunctions.BINARY_TYPE)) {
                relCtxFam.add(readBinaryRelation(relName));
            } else if (type.equals(DatabaseFunctions.SCALING_BINARY_TYPE)) {
                relCtxFam.add(readScalingBinaryRelation(relName));
            }
        }
        return relCtxFam;
    }

    /**
     * @throws BadInputDataException
     * @throws IOException
     */
    public MatrixBinaryRelationBuilder readBinaryRelation(String relName)
                                                                         throws BadInputDataException,
                                                                         IOException {

        Vector obj = dbm.getObjects(relName);
        Vector att = dbm.getAttributes(relName);
        int nbObj = obj.size();
        int nbAtt = att.size();

        MatrixBinaryRelationBuilder binRel = new MatrixBinaryRelationBuilder(
                                                                             nbObj,
                                                                             nbAtt);
        binRel.setName(relName);

        for (int i = 0; i < nbAtt; i++) {
            binRel.replaceAttribute(i, (DefaultFormalAttribute) att.get(i));
        }

        for (int i = 0; i < nbObj; i++) {

            binRel.replaceObject(i, (FormalObject) obj.get(i));
            Vector rel = dbm.getBinaryRelation(relName, obj.get(i).toString());

            for (int j = 0; j < nbAtt; j++) {

                binRel.setRelation(i, j, false);
                String attribute = att.get(j).toString();

                for (int k = 0; k < rel.size(); k++) {

                    if (attribute.equals(rel.get(k).toString())) {
                        binRel.setRelation(i, j, true);
                    }
                }
            }
        }
        return binRel;
    }

    /**
     * @throws BadInputDataException
     * @throws IOException
     */
    public ScalingBinaryRelation readScalingBinaryRelation(String relName)
                                                                          throws BadInputDataException,
                                                                          IOException {

        Vector obj = dbm.getObjects(relName);
        Vector att = dbm.getAttributes(relName);
        int nbObj = obj.size();
        int nbAtt = att.size();

        ScalingBinaryRelation scBinRel = new ScalingBinaryRelation(nbObj, nbAtt);
        scBinRel.setName(relName);

        for (int i = 0; i < nbAtt; i++) {
            scBinRel.replaceAttribute(i, (FormalAttribute) att.get(i));
        }

        for (int i = 0; i < nbObj; i++) {

            scBinRel.replaceObject(i, (FormalObject) obj.get(i));
            Vector rel = dbm.getBinaryRelation(relName, obj.get(i).toString());

            for (int j = 0; j < nbAtt; j++) {

                scBinRel.setRelation(i, j, false);
                String attribute = att.get(j).toString();

                for (int k = 0; k < rel.size(); k++) {

                    if (attribute.equals(rel.get(k).toString())) {
                        scBinRel.setRelation(i, j, true);
                    }
                }
            }
        }
        return scBinRel;
    }

    /*
     * (non-Javadoc)
     * @see java.lang.Runnable#run()
     */
    public void run() {
        try {
            data = readRelationalContext();
        } catch (Exception e) {
            if (jobObserv != null) {
                jobObserv.sendMessage(e.getMessage());
                jobObserv.jobEnd(false);
            }
            return;
        }
        if (jobObserv != null)
            jobObserv.jobEnd(true);
    }

}
