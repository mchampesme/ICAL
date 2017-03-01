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

/*
 * Created on 11 nov. 2003
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package lattice.gui.util;

import java.net.URL;

/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ResourceManager {
	
	public static URL getGaliciaBigImgURL(){
		return ClassLoader.getSystemResource("resources/Galicia.png");
	}
	
	public static URL getGaliciaMinImgURL(){
		return ClassLoader.getSystemResource("resources/GaliciaPetit.png");
	}
	
	public static URL getOpenImgURL(){
		return ClassLoader.getSystemResource("resources/open.gif");
	}

	public static URL getSaveImgURL(){
		return ClassLoader.getSystemResource("resources/save.gif");
	}

	public static URL getCloseImgURL(){
		return ClassLoader.getSystemResource("resources/close.gif");
	}

	public static URL getHelpImgURL(){
		return ClassLoader.getSystemResource("resources/help.gif");
	}
}
