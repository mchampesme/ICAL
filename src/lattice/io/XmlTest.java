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
 * Created on 6 juil. 2003
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package lattice.io;

import java.io.File;

import javax.swing.JFileChooser;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

/**
 * @author roume
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class XmlTest {

	public static void main(String[] args) {
		try{
			// -- créer un document
			DocumentBuilder docBuilder=DocumentBuilderFactory.newInstance().newDocumentBuilder();

			// -- choisir un fichier
			JFileChooser fileChooser = new JFileChooser();
			fileChooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
			fileChooser.setDialogType(JFileChooser.OPEN_DIALOG);
			fileChooser.setMultiSelectionEnabled(false);
			File fich = null;
			int result = fileChooser.showOpenDialog(null);
			if (result == JFileChooser.CANCEL_OPTION
				|| fileChooser.getSelectedFile() == null) {
				System.exit(0);
			} else {
				fich = fileChooser.getSelectedFile();
			}
			
			// -- analyse du fichier
			Document doc=docBuilder.parse(fich);
			
			// -- parcours du fichier
			Element root=doc.getDocumentElement();
			recursPrint(root,"");
			
		}catch (Exception e) {
			e.printStackTrace();
		}
		
	}
	
	public static void recursPrint(Node N, String esp){
		if(N.getNodeType()==Node.TEXT_NODE) System.out.println(esp+N.getNodeValue());
		if(N.getNodeType()==Node.ELEMENT_NODE) {
			System.out.println(esp+((Element)N).getTagName());
			for(int i=0;i<N.getAttributes().getLength();i++){
				System.out.println(esp+"Attr:"+N.getAttributes().item(i).getNodeName()+"="+N.getAttributes().item(i).getNodeValue());
			}
		} 
		for(int i=0;i<N.getChildNodes().getLength();i++){
			recursPrint(N.getChildNodes().item(i),esp+"  ");
		}
	}
}
