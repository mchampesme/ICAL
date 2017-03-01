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

package  lattice.graph.imageButton;

import java.awt.AWTEvent;
import java.awt.AWTEventMulticaster;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.FontMetrics;
import java.awt.Graphics;
import java.awt.Image;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;

import lattice.graph.utils.ChoixComponent;
import lattice.graph.utils.InfoListener;
import lattice.graph.utils.Rectangle3D;
import lattice.graph.utils.ThumbReceiver;

public class ImageButton extends Component implements ChoixComponent, MouseListener, ThumbReceiver {

	static final int META = 20; // Touche pomme
	static final int CTRL = 18; // Touche CTRL
	static final int ALT =  24; // Touche ALT
	static final int SHIFT =  17; // Touche ALT
	static final int CTRLSHIFT =  19; // Touche CTRL+SHIFT
	static final int NORMAL = 16; // Touche Normal
	static final int SHIFTALT = 25; // Touches SHIFT + ALT

	public static String FONT = "Geneva";

	ActionListener actionListener; // Le listener pour gérer les évenements associés au bouton

	private boolean modal = false;
	private boolean selected = false;
	private boolean isDown = false;
	private int borderW = Rectangle3D.borderWidthOfMode(Rectangle3D.IN);
	private boolean affLabel = true;

    /** Left of the image */
    public static final int LEFT = 0;

    /** Top of the image */
    public static final int TOP = 1;

    /** Right of the image */
    public static final int RIGHT = 2;

    /** Bottom of the image */
    public static final int BOTTOM = 3;

	//public String nom;

    private String label, info, infoSelect; // information associée au noeud
	private Image img;
	private Image inactive_img;
	private Image shadowed_img;
	private float imageScale = 1;
//	private AudioClip audio;
	private InfoListener ibm;
	private boolean fShowBorder = true;
	private boolean fDrawPushedIn = true;

    private int	pos = RIGHT;
	private int padding = 2;
	private int gap = 3;

	private int ix=0, iy=0, iw=0, ih=0;	// Internal image info

	private Color color = new Color(210, 210, 210);

	public int choix;

 	public ImageButton(Image image, ActionListener listener, int choix) {
		this(image, null, listener, choix);
		//if(listener instanceof InfoListener) ibm = (InfoListener) listener;
		//initFont(FONT);
	}

// modal = true, le noeud est modal (enfoncé 1 clic sur 2)
	public ImageButton(Image image, boolean modal, ActionListener listener, int choix) {
		this(image, null, listener, choix);
		this.modal = modal; // Par defaut a false
		//addMouseListener(this);
		if(listener instanceof InfoListener) ibm = (InfoListener) listener;
		//initFont(FONT);
	}

// modal = true, le noeud est modal (enfoncé 1 clic sur 2)
	public ImageButton(Image image, String label, boolean modal, ActionListener listener, int choix) {
		this(image, label, listener, choix);
		this.modal = modal; // Par defaut a false
		addMouseListener(this);
		if(listener instanceof InfoListener) ibm =  (InfoListener) listener;
		//initFont(FONT);
	}

 	public ImageButton(Image image, String label, ActionListener listener, int choix) {
		this.label = label;
		//System.out.println("LABEL = "+label);
		img = image;
		initFont(FONT);
		this.choix = choix;
		enableEvents(AWTEvent.MOUSE_EVENT_MASK);
		//setSize(getPreferredSize());
		addActionListener(listener);
		addMouseListener(this);
		if(listener instanceof InfoListener) ibm =  (InfoListener) listener;

    }

    public void initFont(String nomFont) {
    	//System.out.println("set Font"+this);
		super.setFont(new Font(nomFont, Font.PLAIN, 10));
		setSize(getPreferredSize());
    }

// implémente ChoixComponent

	public InfoListener getListener() {
		return ibm;
	}

	public int getChoix() {
		return choix;
	}

// Méthode pour gérer l'aspect modal
	public void setModal(boolean b) {
		modal = b;
	}

	public void setSelected(boolean b) {
		if(selected != b) {
			selected = b;
			repaint();
		}
	}

	public boolean selected() {
		return selected;
	}

 	public void setInfo(String i) {
		info = i;
	}

	public String getInfo() {
		return info;
	}
 	public void setInfoSelect(String i) {
		infoSelect = i;
	}

	public String getInfoSelect() {
		return infoSelect;
	}

	public void setFont(Font f) {
		super.setFont(f);
		setSize(getPreferredSize());
	}

	/** Show the border of the button? Useful when you just want
	 *	the image without the 3D button look around it.
	 */
	public void setShowBorder(boolean b) {
		fShowBorder = b;
		if (b) borderW = Rectangle3D.borderWidthOfMode(Rectangle3D.IN);
		else borderW = 0;
		setSize(getPreferredSize());
	}

	/** Make the button "depress" when clicked? If false the button
	 *	will behave normally, except when pushed it will give no
	 *	visual feedback.
	 */
	public void setDrawPushedIn(boolean b) {
		fDrawPushedIn = b;
	}

    public int getLabelPosition() { return pos; }

	/** Set the position of the label in relation to the image:
	 *	TOP, LEFT, RIGHT or BOTTOM.
	 */
    public void setLabelPosition(int a) {
		if (a != LEFT && a != TOP && a != RIGHT && a != BOTTOM)
					throw new IllegalArgumentException();
		pos = a;
		setSize(getPreferredSize());
   }

    public String getLabel() { return label; }

    public void setLabel(String l) {
		label = l;
		setSize(getPreferredSize());
		repaint();
	}

	/** Set the padding, in pixels, between the button border and
	 *	its image.
	 */
    public void setPadding(int p) {
		padding = p;
		setSize(getPreferredSize());
		repaint();
	}

    public int getPadding() { return padding; }

	/** Set the gap, in pixels, between the label, if any, and image.
	 */
    public void setImageLabelGap(int g) {
		gap = g;
		setSize(getPreferredSize());
		repaint();
	}

    public int getImageLabelGap() { return gap; }

	/** The image to be shown.
	 */
	public void setImage(Image i) {
		if (i == null || img == null) { img = i; setSize(getPreferredSize()); }
		else if (i.getWidth(this) != img.getWidth(this) ||
				i.getHeight(this) != img.getHeight(this)) {
			img = i;
			setSize(getPreferredSize());
		}
		else img = i;
		repaintImage();
	}

// On affiche ou pas le label
	public boolean getAffLabel() {
		return affLabel;
	}

	public void setAffLabel(boolean t) {
		affLabel = t;
	}

	/** Scale the image to the given value (1.0 = 100%).
	 */
	public void setImageScale(double f) { setImageScale((float) f); }

	/** Scale the image to the given value (1.0 = 100%).
	 */
	public void setImageScale(float pct) {
		if (pct <= 0) pct = 1;
		imageScale = pct;
		setSize(getPreferredSize());
	}

/**
	* Active ou desactive le button
 */
	public void setEnabled(boolean b) {
		if (!isEnabled()) {
			isDown = false;
			super.setEnabled(b);
			repaint();
		}
	}

	public boolean selection() {
		return ((selected||isDown) && fDrawPushedIn);
	}

	protected void repaintImage() {
		if (img != null) {
			Graphics g = getGraphics();
			if (g == null) return;
			//g.clearRect(ix, iy, iw, ih);
			//int decalX = (getSize().width - img.getWidth(this))/2;
			//int decalY = (getSize().height - img.getHeight(this))/2;
			if (imageScale == 1)
				g.drawImage(isEnabled() ? img : inactive_img, ix, iy, this);
			else g.drawImage(isEnabled() ? img : inactive_img, ix, iy, iw, ih, this);
		}
	}

	/*protected void calcImgScale() {
		int w = getSize().width;
		int h = getSize().height;
		int iw = img.getWidth(this);
		int ih = img.getHeight(this);
		float fw = (float) iw/ (float) w;
		float fh = (float) ih/ (float) h;
		if(fw>fh) imageScale = fh;
		else imageScale = fw;
	}*/

	public synchronized void paint(Graphics g) {
		g.setFont(getFont());
		/*if (!isEnabled() && inactive_img == null) {
			inactive_img = ImagePanel.createDisabledImage(img, this);
		}*/
		int w = getSize().width;
		int h = getSize().height;

		if (fShowBorder) {
			Rectangle3D r = new Rectangle3D(color, 0, 0, w, h);

			if (selection()) r.setDrawingMode(Rectangle3D.IN);
			else r.setDrawingMode(Rectangle3D.OUT);

			r.paint(g);
		}
		else if(selection()&&(modal)) {// Dessine un carré jaune de sélection
			int xt = 1;
			int yt = 1;
			int wt = w-1;
			int ht = h-1;
			g.setColor(Color.yellow);
			g.drawLine(xt, yt, xt+wt-1, yt);
			g.drawLine(xt, yt, xt, yt+ht-1);
			g.drawLine(xt, yt+ht-1, xt+wt-1, yt+ht-1);
			g.drawLine(xt+wt-1, yt, xt+wt-1, yt+ht-1);
		}

		int o = padding + borderW + (selection() ? 1 : 0);

		iw=0; ih=0;
		int _gap=0;

		//calcImgScale();

		if (img != null) {
			iw = (int) (img.getWidth(this) * imageScale);
			ih = (int) (img.getHeight(this) * imageScale);
			_gap = gap;
		}

		FontMetrics fm=null;

		ix = (int) ((w-iw)/2) + (selection() ? 1 : 0);
		iy = (int) ((h-ih)/2) + (selection() ? 1 : 0);

		if ((label != null)&&(affLabel)) {
			//fm = getFontMetrics(getFont());
			fm = g.getFontMetrics();
			if (pos == RIGHT) ix = o;
			else if (pos == LEFT) ix = o + _gap + fm.stringWidth(label);

			if (pos == TOP) iy = o + _gap + fm.getAscent();
			//else if (pos == BOTTOM) iy = o;
			else if (pos == BOTTOM)  iy -= fm.getAscent()/2;
		}
		repaintImage();

		int x, y;
		if ((label != null)&&(fm != null)&&(affLabel)) {
			//g.setFont(new Font("Geneva", Font.PLAIN, 10));
			if (pos == LEFT) x = o;
			else if (pos == RIGHT) x = o + _gap + iw;
			else x = (int) ((w-fm.stringWidth(label))/2) + (selection() ? 1 : 0);

			if (pos == TOP) y = o + fm.getAscent();
			else if (pos == BOTTOM) {//y = o + _gap + fm.getAscent() + ih;
				 	y = h-(int) (fm.getAscent()/2);
				 }
			else y = h - (int) ((h-fm.getAscent())/2)
						+ (selection() ? 1 : 0) - 1;
			g.setColor(getForeground());
			//			System.out.println((color.getGreen()+color.getRed()+color.getBlue()));
			if((color.getGreen()+color.getRed()+color.getBlue())<400) g.setColor(Color.white);

			if (!isEnabled()) {
				g.setColor(Color.white);
				g.drawString(label, x+1, y+1);
				g.setColor(getBackground().darker());
			}
			//System.out.println(label);
			g.drawString(label, x, y);
		}
	}

	// la taille préférée du bouton : ca dépend du texte qu'il y a dedans
	public Dimension getPreferredSize() {
		Font f = getFont();
		FontMetrics fm = null;
		if ((f != null)&&(label != null)&&(affLabel)) {
			//System.out.println(label);
			fm = getToolkit().getFontMetrics(f);
		}
		int iw=0, ih=0, _gap=0;

		if (img != null) {
			iw = (int) (img.getWidth(this) * imageScale);
			ih = (int) (img.getHeight(this) * imageScale);
			_gap = gap;
		}

		int w, h;
		w = iw + (2*(padding+borderW));
		h = ih + (2*(padding+borderW));

		if (fm != null) {
			if (pos == LEFT || pos == RIGHT) {
				w += _gap + fm.stringWidth(label);

				// Cuz the text could be taller than the image
				h = Math.max(h, fm.getAscent() + (2*(padding+borderW)));
			}
			else {
				h += _gap + fm.getAscent();

				// Cause the text could be wider than the image
				w = Math.max(w, fm.stringWidth(label) + (2*(padding+borderW)));
			}
		}

	//	if(label != null) System.out.print(label);
	//	System.out.println("w = "+w+" h = "+h);
		return new Dimension(w, h);
	}

	// permet d'ajouter un ActionListener au bouton
	public void addActionListener(ActionListener listener) {
		actionListener = AWTEventMulticaster.add(actionListener, listener);
		enableEvents(AWTEvent.MOUSE_EVENT_MASK);
	}
	// enl?ve l'ActionListener passé en param?tres
	public void removeActionListener(ActionListener listener) {
		actionListener = AWTEventMulticaster.remove(actionListener, listener);
	}

	public void setCouleurFond(Color c) {
		color = c;
	}

	public void setChoix(int c) {
		choix = c;
	}

	protected void afficherInfo() {
		if(! selected) {
			if((getInfo() != null) && (getListener() != null)) getListener().setInfo(getInfo());
		}
		else if((getInfoSelect() != null) && (getListener() != null)) getListener().setInfo(getInfoSelect());
	}

// implémente MouseListener
	public void mouseEntered(MouseEvent e) {
		afficherInfo();
	}
	public void mouseExited(MouseEvent e) {
		if((getInfo() != null) && (getListener() != null)) getListener().removeInfo();
		if (isEnabled() && isDown) {
			isDown = false;
			repaint();
		}
	}

	public void mousePressed(MouseEvent e) {
		if (isEnabled()) {
			isDown = true;
			repaint();
		}
	}
	public void mouseReleased(MouseEvent e) {
		if (isEnabled() && isDown) {
			isDown = false;
			if(e.getClickCount() >= 2) {
				if(modal) selected = true;
				performAction(ActionEvent.CTRL_MASK);
			}
			else {
				if(modal) {
					if(selected) selected=false;
					else selected = true;
				}
				else selected = false;
				if(actionListener != null) {
					switch(e.getModifiers()) {
						case META: performAction(ActionEvent.META_MASK); break;
						case CTRL: performAction(ActionEvent.CTRL_MASK); break;
						case ALT: performAction(ActionEvent.ALT_MASK); break;
						case SHIFT: performAction(ActionEvent.SHIFT_MASK); break;
						case CTRLSHIFT: performAction(ActionEvent.SHIFT_MASK+ActionEvent.META_MASK); break;
						default: performAction(0); break;
					}
				}
			}
			repaint();
		}
	}

	public void performAction(int action) {
		actionListener.actionPerformed(new ActionEvent(this, ActionEvent.ACTION_PERFORMED, label, action));
		//System.out.println(selected);
		//if(modal) setSelected(! selected());
	}

	public void mouseClicked(MouseEvent e) {
		afficherInfo();
	}

 // Implémente ThumbReceiver
 /**
 	* Lorsque l'image réduite arrive de mani?re asynchrone
 */
 	public void imageReady(Image imgRed, String nomFich, int index, boolean invalide) {
 		if(nomFich != null) this.label = nomFich;
 		else this.label = "";
 		if(! invalide) {
 			if(imgRed != null) this.img = imgRed;
 			//initFont("Geneva");
 			repaint();
 		}
 		//else System.out.println("Image invalide : "+nomFich);
 	}
 	public void imageReady2(Image imgRed, String nomFich, int index, boolean invalide) {}


 }