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
 * Created on Jun 27, 2004
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package lattice.io.xmigateway;

import java.io.IOException;
import java.util.ArrayList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;
import org.xml.sax.InputSource;

/**
 * @author rouanehm
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class XmiDomParser {
	
	private XmiData xmiData;  
	private Element root;
	
	public XmiDomParser(InputSource is){
		xmiData = new XmiData();
		try {
			DocumentBuilderFactory builderFactory = DocumentBuilderFactory.newInstance();
			DocumentBuilder builder = builderFactory.newDocumentBuilder();
			Document document = builder.parse(is);
			// load document in memory
			root = (Element) document.getDocumentElement();			
		}
		catch(ParserConfigurationException ex) {
			ex.printStackTrace();
		}
		catch(SAXException ex) {
			ex.printStackTrace();
		}
		catch(IOException ex) {
			ex.printStackTrace();
		}        
		xmiData = new XmiData();	
	}

	public XmiData loadXMIData(){		
		NodeList models = root.getElementsByTagName("UML:Model");
		Node node = models.item(0);		
		NamedNodeMap attributes = node.getAttributes();
		Node modelName = attributes.getNamedItem("name");		
		//XMIParserView.appendResultLogText("ModelName: "+modelName.getNodeValue()+"\n");
		xmiData.setModelName(modelName.getNodeValue());
		loadClasses();
		loadAssociations();	
		return xmiData;
	}

 	public void loadClasses() {
		NodeList classes = root.getElementsByTagName("UML:Class");
		for(int i=0;i<classes.getLength();i++){ 		
			Node node=classes.item(i);
			NamedNodeMap attributes = node.getAttributes();
   			Node className = attributes.getNamedItem("name");
   			Node classID = attributes.getNamedItem("xmi.id");
			XmiClass newXMIClass = new XmiClass(classID.getNodeValue(),className.getNodeValue());
			ArrayList xmiAttrs=loadAttributes((Element) node);
			newXMIClass.setXMIAttributes(xmiAttrs);
			xmiData.appendClass(newXMIClass);
 		}
 	}
	public void loadAssociations() {
		NodeList associations = root.getElementsByTagName("UML:Association");
		for(int i=0;i<associations.getLength();i++){ 		
			Node node=associations.item(i);
			NamedNodeMap attributes = node.getAttributes();
			Node assocID = attributes.getNamedItem("xmi.id");
			Node assocName = attributes.getNamedItem("name");
			NodeList roles = ((Element)node).getElementsByTagName("UML:AssociationEnd");
			XmiAssociationEnd firstRole=null, secondRole=null;
			// filling roles
			if(roles.getLength()>0){
				Node localNode = roles.item(0);
				firstRole=getAssociationEnd(localNode);				
				secondRole=getAssociationEnd(roles.item(1)); 
			}
			XmiAssociation newXMIAssoc = new XmiAssociation(assocID.getNodeValue(),assocName.getNodeValue(),firstRole,secondRole);
			xmiData.appendAssoc(newXMIAssoc);
		}	 			
	}
	
	/**
	 * @param node
	 * @return
	 */
	private XmiAssociationEnd getAssociationEnd(Node node) {
		NamedNodeMap roleAttributes=node.getAttributes();
		Node roleId = roleAttributes.getNamedItem("xmi.id");
		Node roleName = roleAttributes.getNamedItem("name");
		Node refClass = roleAttributes.getNamedItem("type");
		String temp=refClass.getNodeValue();
		String className = getClassName(temp);
		Node navigation = roleAttributes.getNamedItem("isNavigable");
		NodeList multiplicity= ((Element)node).getElementsByTagName("UML:MultiplicityRange");
		Node MultNode=multiplicity.item(0);
		NamedNodeMap multiplicityAttr=MultNode.getAttributes(); 
		Node lowerMult = multiplicityAttr.getNamedItem("lower");
		Node upperMult = multiplicityAttr.getNamedItem("upper");
		XmiAssociationEnd role = new XmiAssociationEnd(roleId.getNodeValue(),roleName.getNodeValue(),
		className,lowerMult.getNodeValue(),upperMult.getNodeValue(),navigation.getNodeValue());						
		return role;
	}

	/**
	 * @param string
	 * @return
	 */
	private String getClassName(String classID) {
		// will be replaced soon by nodeFromID
		return xmiData.getClass(classID);
	}

	public ArrayList loadAttributes(Element object) {		
		NodeList attrs = object.getElementsByTagName("UML:Attribute");
		if(attrs.getLength()==0) return null;
		ArrayList attrsList = new ArrayList();
		for(int i=0;i<attrs.getLength();i++){ 		
			Node node=attrs.item(i);
			NamedNodeMap attributes = node.getAttributes();
			Node attrID = attributes.getNamedItem("xmi.id");
			Node attrName = attributes.getNamedItem("name");
			Node attrType = attributes.getNamedItem("type");
			String typeid=attrType.getNodeValue();
			String type=getClassAttributType(typeid);
			XmiAttribute newXMIAttr= new XmiAttribute(attrID.getNodeValue(),attrName.getNodeValue(),type);
			attrsList.add(newXMIAttr);	
		}	
 		return attrsList;
	}

	private String getClassAttributType(String typeid) {
		NodeList types = root.getElementsByTagName("UML:DataType");
		for(int i=0;i<types.getLength();i++){ 
			Node node=types.item(i);
			NamedNodeMap attributes = node.getAttributes();
			Node id = attributes.getNamedItem("xmi.id");
			Node typename = attributes.getNamedItem("name");
			if(id.getNodeValue().compareTo(typeid)==0) return typename.getNodeValue();
		}
		return "UNKOWN TYPE";
		
	}
	
}