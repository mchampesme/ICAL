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
import java.util.SortedSet;
import lattice.alpha.util.BGIntent;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;

		Object leClone = null;
			leClone = super.clone();
		} catch (CloneNotSupportedException e) {
			throw new InternalError();
		}
		//if(getExtension() == null) System.out.println("Attention extension null !!!");
		m.items = items.clone();
		m.extension = extension.clone();
 * Calcul la fermeture de this Ens. des items Ai, t.q. spc(M+Ai) = spc(M) FI1 :
 * Vecteur des 1-motif fréquent
 */
	public Itemset fermeture(List<Itemset> FI1) {
		Itemset result = (Itemset) this.clone(); // This augmenté des items
													// Ai
		for (int i = 0; i < FI1.size(); i++) {
			Itemset m1 = FI1.get(i);
			if (!this.contains(m1.items.first())) {
				Itemset m2 = (Itemset) this.clone();
				m2.addMotif(m1);
				if (m2.getSupport() == this.getSupport()) {
					result.addMotif(m1);
				}
			}
		}
		return result;
	}