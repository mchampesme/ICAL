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

package lattice.io;

import java.io.IOException;
import java.io.Writer;

import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.InterObjectBinaryRelation;
import lattice.util.relation.RelationalContextFamily;
import lattice.util.relation.ScalingBinaryRelation;

/**
 * @author Mr ROUME To change this generated comment edit the template variable
 *         "typecomment": Window>Preferences>Java>Templates. To enable and
 *         disable the creation of type comments go to
 *         Window>Preferences>Java>Code Generation.
 */
public class RcfWriter extends AbstractWriter implements
        RelationalContextWriter {

    /**
     * Constructor for ContextWriter.
     * 
     * @param w
     */
    public RcfWriter(Writer w) {
        super(w);
    }

    /**
     * @see AbstractWriter#writeRelationalContext(RelationalContext)
     */
    public void writeRelationalContext(RelationalContextFamily relCtx)
                                                                      throws IOException {
        getStream().write("[Relational Context]\n");
        getStream().write(relCtx.getName() + "\n");
        for (int i = 0; i < relCtx.size(); i++) {
            if (relCtx.get(i) instanceof InterObjectBinaryRelation)
                writeInterObjectBinaryRelation((InterObjectBinaryRelation) relCtx
                        .get(i));
            else if (relCtx.get(i) instanceof ScalingBinaryRelation)
                writeScalingBinaryRelation((ScalingBinaryRelation) relCtx
                        .get(i));
            else if (relCtx.get(i) instanceof MatrixBinaryRelationBuilder)
                writeBinaryRelation((MatrixBinaryRelationBuilder) relCtx.get(i));

            sendJobPercentage((i * 100) / relCtx.size());

        }
        getStream().write("[END Relational Context]\n");
        getStream().close();

        sendJobPercentage(100);

    }

    public void writeBinaryRelation(MatrixBinaryRelationBuilder binRel) throws IOException {
        getStream().write("[Binary Relation]\n");
        getStream().write(binRel.getName() + "\n");
        FormalObject[] lesObjs = binRel.getFormalObjects();
        FormalAttribute[] lesAtts = binRel.getFormalAttributes();
        String line = "";
        for (int i = 0; i < lesObjs.length; i++) {
            line = line + lesObjs[i].toString() + " | ";
        }
        getStream().write(line + "\n");
        line = "";
        for (int j = 0; j < lesAtts.length; j++) {
            line = line + lesAtts[j].toString() + " | ";
        }
        getStream().write(line + "\n");
        for (int i = 0; i < lesObjs.length; i++) {
            line = "";
            for (int j = 0; j < lesAtts.length; j++) {
                if (binRel.getRelation(lesObjs[i], lesAtts[j]).isFalse()) {
                    line = line + "0 ";
                } else {
                    line = line + "1 ";
                }
            }
            getStream().write(line + "\n");
        }
        getStream().flush();
    }

    public void writeInterObjectBinaryRelation(
                                               InterObjectBinaryRelation ioBinRel)
                                                                                  throws IOException {
        getStream().write("[Inter Object Binary Relation]\n");
        getStream().write(ioBinRel.getName() + "\n");
        // Added by Amine
        getStream().write(ioBinRel.getObjectsContextName() + "\n");
        getStream().write(ioBinRel.getAttributesContextName() + "\n");
        // end Amine modifs

        FormalObject[] lesObjs = ioBinRel.getFormalObjects();
        FormalAttribute[] lesAtts = ioBinRel.getFormalAttributes();
        String line = "";
        for (int i = 0; i < lesObjs.length; i++) {
            line = line + lesObjs[i].toString() + " | ";
        }
        getStream().write(line + "\n");
        line = "";
        for (int j = 0; j < lesAtts.length; j++) {
            line = line + lesAtts[j].toString() + " | ";
        }
        getStream().write(line + "\n");
        for (int i = 0; i < lesObjs.length; i++) {
            line = "";
            for (int j = 0; j < lesAtts.length; j++) {
                if (ioBinRel.getRelation(lesObjs[i], lesAtts[j]).isFalse()) {
                    line = line + "0 ";
                } else {
                    line = line + "1 ";
                }
            }
            getStream().write(line + "\n");
        }
        getStream().flush();

    }

    public void writeScalingBinaryRelation(ScalingBinaryRelation scBinRel)
                                                                          throws IOException {
        getStream().write("[Scaling Binary Relation]\n");
        getStream().write(scBinRel.getName() + "\n");
        FormalObject[] lesObjs = scBinRel.getFormalObjects();
        FormalAttribute[] lesAtts = scBinRel.getFormalAttributes();
        String line = "";
        for (int i = 0; i < lesObjs.length; i++) {
            line = line + lesObjs[i].toString() + " | ";
        }
        getStream().write(line + "\n");
        line = "";
        for (int j = 0; j < lesAtts.length; j++) {
            line = line + lesAtts[j].toString() + " | ";
        }
        getStream().write(line + "\n");
        for (int i = 0; i < lesObjs.length; i++) {
            line = "";
            for (int j = 0; j < lesAtts.length; j++) {
                if (scBinRel.getRelation(lesObjs[i], lesAtts[j]).isFalse()) {
                    line = line + "0 ";
                } else {
                    line = line + "1 ";
                }
            }
            getStream().write(line + "\n");
        }

        getStream().flush();
    }

    public void run() {
        try {
            writeRelationalContext((RelationalContextFamily) data);
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
