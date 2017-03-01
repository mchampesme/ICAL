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

package rule.util;// import javaimport java.util.Iterator;import java.util.List;
import java.util.SortedSet;import java.util.TreeSet;import java.util.Vector;import lattice.alpha.util.BGExtent;
import lattice.alpha.util.BGIntent;
import lattice.util.concept.Extent;
import lattice.util.concept.FormalAttribute;import lattice.util.concept.Intent;
/**	* Repr�sentation d'un motif : ens. d'attributs avec le support	* @author David Grosser	* @date 20 Mai 2003*/public class Itemset implements Cloneable {	protected Intent items; // L'ensemble des attributs formels	protected Extent extension; // L'extension du Motif// constructeur	public Itemset() {		items = new BGIntent();	}	public Itemset(FormalAttribute f) {		this();		items.add(f);	}	public Itemset(Intent items) {		this.items = new BGIntent(items);	}	public Itemset(TreeSet<FormalAttribute> items) {		this.items = new BGIntent(items);	}// M�thodes de traitement	public Intent getItems() {		return items;	}		public void addItem(FormalAttribute f) {		items.add(f);	}		public void addItems(TreeSet<FormalAttribute> t) {		items.addAll(t);	}	public void addItems(Itemset m) {		items.addAll(m.getItems());	}	public Extent getExtension() {		return extension;	}		public int getSupport() {		return extension.size();	}	public String toString() {		return new String(items+"\t"+getExtension()+"\n");	}	public boolean contains(Object o) {		return items.contains(o);	}	public boolean containsAll(Itemset f) {		for(Iterator<FormalAttribute> it = f.getItems().iterator(); it.hasNext() ;)			if(! items.contains(it.next())) return false;		return true;		}	public boolean containsAll(SortedSet<FormalAttribute> f) {		for(Iterator<FormalAttribute> it = f.iterator(); it.hasNext() ;)			if(! items.contains(it.next())) return false;		return true;		}/**	* Clonage d'un motif*/	public Itemset clone() {		//System.out.println(this);
		Object leClone = null;		try {
			leClone = super.clone();
		} catch (CloneNotSupportedException e) {
			throw new InternalError();
		}		Itemset m = (Itemset) leClone;
		//if(getExtension() == null) System.out.println("Attention extension null !!!");		//TreeSet t = new TreeSet(getExtension());
		m.items = items.clone();
		m.extension = extension.clone();		return m;	}	public boolean equals(Object o) {		return getItems().equals(((Itemset) o).getItems());	} /**	* Ajout d'un motif*/	public boolean addMotif(Itemset m) {		boolean b = items.addAll(m.getItems());		if(b) extension.retainAll(m.getExtension());		return b;	}	/**	* retourne l'union de this avec m*/		public Itemset union(Itemset m) {		if(isEmpty()) return (Itemset) m.clone();		Itemset union = (Itemset) this.clone();		union.addMotif(m);		return union;			}/**	* Retourne true si this est un motif vide*/	public boolean isEmpty() {		return getItems().isEmpty();	}/**
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
	}/**	* Retourne la taille du motif (nbre d'items)*/	public int size() {		return items.size();	}/**	* this - m*/	public TreeSet difference(Itemset m) {		TreeSet diff = (TreeSet) getItems().clone();		diff.removeAll(m.getItems());		return diff;	}}