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

package lattice.command;import java.util.StringTokenizer;import java.util.Vector;/**	* Un �valuateur pour ex�cuter des commandes textuelles	* @author David Grosser	* @date 30 Mai 2003*/public abstract class Command {// Variables d'instance	String function;	Vector<String> args = new Vector<String>();	// M�thodes	public abstract void eval(String s);	public void parsing(String s) {		StringTokenizer st = new StringTokenizer(s, " ");		if(st.hasMoreTokens()) {			String tempo = st.nextToken();			if(tempo.equals(">")) st.nextToken();			while(st.hasMoreTokens()) {				//System.out.println("*"+st.nextToken()+"*");				args.add(st.nextToken());			}		}			}}