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

package lattice.gui;// import javaimport java.awt.BorderLayout;import java.awt.Font;import java.awt.event.ActionEvent;import java.awt.event.ActionListener;import javax.swing.JPanel;import javax.swing.JScrollPane;import javax.swing.JTextArea;import javax.swing.JTextField;import lattice.command.Command;/**	* La console	* @author D. Grosser*/public class Console extends JPanel implements MessageWriter, ActionListener {	protected Command cmd;		protected String prompt ="> ";	protected JTextArea output;	protected JTextField input;	/**	 * Constructor for Console.*/	public Console() {		init1();	}	public Console(String inv) {		this();	   	prompt = inv;	}	public Console(Command c) {		cmd = c;		init2();	}	public Console(Command c, String inv) {		cmd = c;		prompt = inv;		init2();	}	public void addMessage(String newMess) {		output.append(newMess+"\n");	}		public void clear() {		output.setText("");	}	public void init1() {		setLayout(new BorderLayout());		initOutput() ;		add(new JScrollPane(output), BorderLayout.CENTER);	}	public void init2() {		setLayout(new BorderLayout());		initOutput() ;		initInput() ;		add(new JScrollPane(output), BorderLayout.CENTER);		add(input, BorderLayout.SOUTH) ;		input.addActionListener(this) ;	}	public void initOutput() {	   output = new JTextArea() ;	   output.setEditable(false) ;	   output.setFont(new Font("Geneva", Font.PLAIN, 11)) ;	}	public void initInput() {		input = new JTextField(prompt) ;		//input.setBackground(Color.black);	   	//input.setForeground(Color.white);	}	public void actionPerformed(ActionEvent e) {		String s = e.getActionCommand() ;		addMessage(s) ;		input.setText(prompt) ;		cmd.eval(s);	}		public String getText(){		return output.getText();	}}