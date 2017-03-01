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

package lattice.gui.graph.control;

// import java
import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;

import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComponent;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JSlider;
import javax.swing.JTextField;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import lattice.graph.utils.BorderedPanel;
import lattice.gui.graph.LatticeGraphViewer;
import lattice.gui.graph.magneto.Magneto;
/**
 * <p>Titre : Lattice</p>
 * <p>Description : Manipulation des treillis. Panel de control de l'affichage du treillis</p>
 * <p>Copyright : Copyright (c) 2002</p>
 * <p>Société : Université de Montréal</p>
 * @author David Grosser
 * @version 1.0
 */

public class LGControlPanel extends JPanel {

  public static Color back = new Color(70, 70, 100);

// Constantes pour la gestion des actions
  public static final int FORMATTER = 1; // Jbutton
  public static final int FIT_SCREEN = 2; // JCheckBox
  public static final int OPTIMIZE = 3; // JCheckBox
  public static final int ZOOM_PLUS = 4; // JButton
  public static final int ZOOM_MOINS = 5; // JButton

  public static final int MAGNET = 10; // JCheckBox
  public static final int TIME_SLEEP = 11; // JTextField
  public static final int TIME_SLIDE = 12;
  public static final int REPULSION = 13; // JTextField TRepulsion
  public static final int REPULSION_SLIDE = 14; //  Slide Repulsion
  public static final int TENSION = 15; // JTextFiedl TTension
  public static final int TENSION_SLIDE = 16; // JTextFiedl TTension
  public static final int STEP = 17;

  public static final int FIX_FIRST_LEVEL = 18;
  public static final int FIX_LAST_LEVEL = 19;
  public static final int FIX_BOTTOM = 20;
  public static final int MAGNET_RELATIONS = 21;
  public static final int MAGNET_MOUSE = 22;

  public static final int THREE_D = 30;
  public static final int ROTATION = 31;

  public boolean fitScreen = false;
  public boolean optimizer = false;
  public boolean magnet = false;

  public JSlider sr, st, stime, srot;

  public LatticeGraphViewer lgv;
  // Constructeur
  public LGControlPanel(LatticeGraphViewer lgv) {
    //super(WITHOUT_RIGHT, 0, 29) ;
    super() ;
    this.lgv = lgv;
    //this.parent = parent;
    try {
      jbInit();
      } catch(Exception e) {;}
  }

/*    protected void initRessources() {
      ressources = new Ressources(this);
  //ressources.defautJarDirectory = "ikbs/ressources/illustration";
      ressources.defautJarDirectory = "/ressources";
      ressources.setAcces(Ressources.FROM_JAR);
      ressources.setLocal(false);
      ressources.wait = true;
      try{
        ressources.init(nomImages);
      }catch(Exception e) {System.out.println("Probl?me d'acc?s aux ressources (PanelButonIllu)");}
    }*/

  public Magneto getMagneto() {
    return lgv.getMagneto();
  }

  private void jbInit() throws Exception {
    //Container c = this.getContentPane();
    setLayout(new FlowLayout(0));
    JPanel c = new JPanel();
    c.setLayout(new BorderLayout(10, 0));
    c.setOpaque(false);
    add(c);
    //initRessources();
    //initGridBagConstraint();
    //c.insets=new Insets(0, 0, 0, 0);
    setOpaque(false);
    //setLayout(new BorderLayout(5, 5));
    //setLayout(new FlowLayout(3));
    //setBackground(new Color(50, 50, 80));
    //pba = new ArbreAdapter(0, parent);

    c.add(initFormat(), BorderLayout.NORTH);

    c.add(initMagnet(), BorderLayout.CENTER);

    c.add(init3D(), BorderLayout.SOUTH);

    validate();

  } // fin init

public JPanel init3D() {
  BorderedPanel p3D = new BorderedPanel("           ", Color.white);
  p3D.setLayout(new GridBagLayout());
  p3D.initGridBagConstraint();
  p3D.c.insets = new Insets(3, 5, 3, 4);

  //JLabel test = new JLabel("      ");
  //p3D.xyPosition(p3D, test, 0, 0, 1);
  //test.setOpaque(false);

  JCheckBox c3D = new JCheckBox("3D", false);
  c3D.setForeground(Color.white);
  c3D.setOpaque(false);
  p3D.xyPosition(p3D, c3D, 0, 1, 1);
  c3D.addItemListener(new Controler(THREE_D));


    /*JCheckBox cRotation = new JCheckBox("Rotation", getMagneto().getRotation());
    cRotation.setForeground(Color.white);
    cRotation.setOpaque(false);
    p3D.xyPosition(p3D, cRotation, 1, 2, 2, GridBagConstraints.REMAINDER);
    cRotation.addItemListener(new Controler(ROTATION));
    cRotation.setToolTipText("Rotation");*/
    JLabel lRot = new JLabel("Rotation   ");
    lRot.setForeground(Color.white);
    lRot.setToolTipText("Rotation the 3D lattice model left or right");
    p3D.xyPosition(p3D, lRot, 0, 2, 1);
    // Le slider tension
    srot = new JSlider(JSlider.HORIZONTAL, 0, 20, 10)
    {
      public Dimension getPreferredSize() {return new Dimension(70, 25);}
    };
    //srot.setSize(100, 25);
    srot.addChangeListener(new Controler(ROTATION, null, 10));
    srot.setMajorTickSpacing(1);
    srot.setOpaque(false);
    srot.setBackground(back);
    p3D.xyPosition(p3D, srot, 1, 2, 1, GridBagConstraints.REMAINDER);


  return p3D;
}

  /**
   * Initialisation du panel contenant les options de formatage du treillis
   */
  public JPanel initFormat() {

// Définition des Panels
    BorderedPanel pFormat = new BorderedPanel("Format", Color.white);
    //pMagnet.setBackground(back);
    pFormat.setLayout(new GridBagLayout());
    pFormat.initGridBagConstraint();
    pFormat.c.insets = new Insets(3, 5, 3, 4);
    //ImageButton bFormat = new ImageButton(getToolkit().getImage(MainView.RESSOURCES+"open.gif"), this, 1);
    //   ImageButton bFormat = new ImageButton(getToolkit().getImage(MainView.RESSOURCES+"open.gif"), this, 1);
    //JButton bFormat = new JButton(new ImageIcon(MainView.RESSOURCES+"open.gif"));

/*    JButton bFormat2 = new JButton("Formatter2");
    xyPosition(pFormat, bFormat2, 0, 1, 1);
    JButton bFormat3 = new JButton("Formatter3");
    xyPosition(pFormat, bFormat3, 0, 2, 1);*/

    JLabel test = new JLabel("      ");
    pFormat.xyPosition(pFormat, test, 0, 0, 1);
    test.setOpaque(false);

    JCheckBox cFitScreen = new JCheckBox("Fit      ", false);
    cFitScreen.setForeground(Color.white);
    cFitScreen.setOpaque(false);
    pFormat.xyPosition(pFormat, cFitScreen, 0, 1, 1);
    cFitScreen.addItemListener(new Controler(FIT_SCREEN));
    cFitScreen.setToolTipText("Format lattice in order to fit screen size");

    JCheckBox cOptimize = new JCheckBox("Optimize", false);
    cOptimize.setForeground(Color.white);
    cOptimize.setOpaque(false);
    pFormat.xyPosition(pFormat, cOptimize, 1, 1, 1);
    cOptimize.addItemListener(new Controler(OPTIMIZE));
    cOptimize.setToolTipText("Optimize arrangement of nodes in each level");

    JButton bFormat1 = new JButton("Format");
    pFormat.xyPosition(pFormat, bFormat1, 0, 3, 2, GridBagConstraints.REMAINDER);
    bFormat1.addActionListener(new Controler(FORMATTER));

    JButton bZoomP = new JButton("+");
    pFormat.xyPosition(pFormat, bZoomP, 0, 4, 1);
    bZoomP.addActionListener(new Controler(ZOOM_PLUS));

    JButton bZoomM = new JButton("-");
    pFormat.xyPosition(pFormat, bZoomM, 1, 4, 1);
    bZoomM.addActionListener(new Controler(ZOOM_MOINS));

    //pFormat.xyPosition(pFormat, new JLabel("Width constraint"), 0, 3, 1);
    //JTextField WConstraint = new JTextField(140);
    //pFormat.xyPosition(pFormat, WConstraint, 0, 3, 1);

    //c.add(pFormat, BorderLayout.NORTH);
    return pFormat;
  }

  public JPanel initMagnet() {
// Le Panel Magneto

    BorderedPanel pMagnet = new BorderedPanel("                       ");
    //pMagnet.setBackground(back);
    pMagnet.setLayout(new GridBagLayout());
    pMagnet.initGridBagConstraint();
    pMagnet.c.insets=new Insets(3, 5, 3, 4);

    JLabel test2 = new JLabel("   ");
    test2.setOpaque(false);
    //pMagnet.xyPosition(pMagnet, test2, 0, 0, 1);

    //pMagnet.xyPosition(pMagnet, new JLabel("Magnet"), 0, 0, 1);
    JCheckBox cMagnet = new JCheckBox("Magnetism", false);
    cMagnet.setForeground(Color.white);
    cMagnet.setOpaque(false);
    pMagnet.xyPosition(pMagnet, cMagnet, 0, 1, 2, GridBagConstraints.REMAINDER);
    cMagnet.addItemListener(new Controler(MAGNET));
    cMagnet.setToolTipText("Magnet the distance beetween nodes");

// TimeSleep
    JLabel lTime = new JLabel("Time sleep");
    lTime.setForeground(Color.white);
    lTime.setToolTipText("Period beetween two iterations");
    pMagnet.xyPosition(pMagnet, lTime, 0, 2, 1);
    long defaultTimeSleep = getMagneto().getTimeSleep();
    JTextField TtimeSleep = new JTextField(new Long(defaultTimeSleep).toString());
    TtimeSleep.addActionListener(new Controler(TIME_SLEEP, TtimeSleep, defaultTimeSleep));
    //pMagnet.xyPosition(pMagnet, TtimeSleep, 1, 2, 1);

    // Le slider timesleep
    stime = new JSlider(JSlider.HORIZONTAL, 0, 800, (int) defaultTimeSleep)
    {
      public Dimension getPreferredSize() {return new Dimension(40, 25);}
    };
    //stime.setSize(40, 25);
    stime.addChangeListener(new Controler(TIME_SLIDE, TtimeSleep, defaultTimeSleep));
    stime.setMajorTickSpacing(10);
    stime.setOpaque(false);
    stime.setBackground(back);
    stime.setMinorTickSpacing(1);
    //stime.createStandardLabels(1);
    //stime.setPaintLabels(true);
    //pMagnet.c.insets=new Insets(0, 5, 8, 5);
    //pMagnet.xyPosition(pMagnet, sr, 0, 6, 2, GridBagConstraints.REMAINDER);
    pMagnet.xyPosition(pMagnet, stime, 1, 2, 2, GridBagConstraints.REMAINDER);

    /*pMagnet.xyPosition(pMagnet, new JLabel("Step"), 0, 2, 1);
    int defaultStep = getMagneto().getPas();
    JTextField Tstep = new JTextField(new Integer(defaultStep).toString());
    Tstep.addActionListener(new Controler(STEP, Tstep, defaultStep));
    pMagnet.xyPosition(pMagnet, Tstep, 1, 2, 1);*/

// Tension
    JLabel lTension = new JLabel("Tension");
    lTension.setForeground(Color.white);
    lTension.setToolTipText("Tension of the links beetween nodes");
    pMagnet.xyPosition(pMagnet, lTension, 0, 3, 1);
    double defaultTension = getMagneto().getTensionFactor();
    JTextField Ttension = new JTextField(new Double(defaultTension).toString());
    Ttension.addActionListener(new Controler(TENSION, Ttension, defaultTension));
    //pMagnet.xyPosition(pMagnet, Ttension, 1, 3, 1);

    // Le slider tension
    st = new JSlider(JSlider.HORIZONTAL, 0, 300, (int) defaultTension*10)
    {
      public Dimension getPreferredSize() {return new Dimension(60, 25);}
    };
    st.setSize(40, 25);
    st.addChangeListener(new Controler(TENSION_SLIDE, Ttension, defaultTension));
    st.setMajorTickSpacing(1);
    st.setOpaque(false);
    st.setBackground(back);
    //st.createStandardLabels(1);
    //st.setPaintLabels(true);
    //st.setMinorTickSpacing(1);
    //pMagnet.c.insets=new Insets(0, 5, 8, 5);
    //pMagnet.xyPosition(pMagnet, st, 1, 4, 2, GridBagConstraints.REMAINDER);
    pMagnet.xyPosition(pMagnet, st, 1, 3, 2, GridBagConstraints.REMAINDER);
    //pMagnet.c.insets=new Insets(3, 5, 3, 5);

// Repulsion
    JLabel jRepulsion = new JLabel("Repulsion");
    jRepulsion.setForeground(Color.white);
    jRepulsion.setToolTipText("Repulsion force beetween nodes");
    pMagnet.xyPosition(pMagnet, jRepulsion, 0, 5, 1);
    double defaultRepulsion = getMagneto().getRepulsionFactor();
    Double dou = new Double( ((double) defaultRepulsion)*10.0);
    JTextField Trepulsion = new JTextField(dou.toString());

    Trepulsion.addActionListener(new Controler(REPULSION, Trepulsion, defaultRepulsion));
    //pMagnet.xyPosition(pMagnet, Trepulsion, 1, 5, 1);

    int t = (int) (100.0 * defaultRepulsion);
    // Le slider repulsion
    sr = new JSlider(JSlider.HORIZONTAL, 0, 80, t)
       //sr.setSize(40, 25);
    {
      public Dimension getPreferredSize() {return new Dimension(60, 25);}
    };
    sr.addChangeListener(new Controler(REPULSION_SLIDE, Trepulsion, defaultRepulsion));
    sr.createStandardLabels(1);
    sr.setOpaque(false);
    sr.setBackground(back);
    //sr.setPaintLabels(true);
    //sr.setMajorTickSpacing(1);
    //sr.setMinorTickSpacing(1);
    //pMagnet.c.insets=new Insets(0, 5, 8, 5);
    //pMagnet.xyPosition(pMagnet, sr, 0, 6, 2, GridBagConstraints.REMAINDER);
    pMagnet.xyPosition(pMagnet, sr, 1, 5, 2, GridBagConstraints.REMAINDER);
    //pMagnet.c.insets=new Insets(3, 5, 3, 5);

    /*JLabel jUnlink = new JLabel("Unlink");
    jUnlink.setForeground(Color.white);
    jUnlink.setToolTipText("Minimal distance to unlink nearest nodes");
    pMagnet.xyPosition(pMagnet, jUnlink, 0, 5, 1);
    JTextField Tunlink = new JTextField(new Double(lgv.magneto.unlink).toString());
    pMagnet.xyPosition(pMagnet, Tunlink, 1, 5, 1);*/

    JCheckBox cfixFirstLevel = new JCheckBox("Fix first", getMagneto().fixFirstLevel());
    cfixFirstLevel.setForeground(Color.white);
    cfixFirstLevel.setOpaque(false);
    pMagnet.xyPosition(pMagnet, cfixFirstLevel, 0, 7, 1);
    cfixFirstLevel.addItemListener(new Controler(FIX_FIRST_LEVEL));
    cfixFirstLevel.setToolTipText("Fix first level nodes position");

    JCheckBox cfixLastLevel = new JCheckBox("Fix last", getMagneto().fixLastLevel());
    cfixLastLevel.setForeground(Color.white);
    cfixLastLevel.setOpaque(false);
    pMagnet.xyPosition(pMagnet, cfixLastLevel, 1, 7, 1);
    cfixLastLevel.addItemListener(new Controler(FIX_LAST_LEVEL));
    cfixLastLevel.setToolTipText("Fix last level nodes position");

    /*JCheckBox cfixBottom = new JCheckBox("Fix Bottom", getMagneto().fixBottom());
    cfixBottom.setForeground(Color.white);
    cfixBottom.setOpaque(false);
    pMagnet.xyPosition(pMagnet, cfixBottom, 0, 8, 2, GridBagConstraints.REMAINDER);
    cfixLastLevel.addItemListener(new Controler(FIX_BOTTOM));
    cfixLastLevel.setToolTipText("Fix bottom position");*/

    JCheckBox cMagnetRelation = new JCheckBox("Relation", getMagneto().magnetRelation());
    cMagnetRelation.setForeground(Color.white);
    cMagnetRelation.setOpaque(false);
    pMagnet.xyPosition(pMagnet, cMagnetRelation, 0, 9, 1);
    cMagnetRelation.addItemListener(new Controler(MAGNET_RELATIONS));
    cMagnetRelation.setToolTipText("Magnet cross relations");

    JCheckBox cMagnetMouse = new JCheckBox("Mouse", getMagneto().magnetMouse());
    cMagnetMouse.setForeground(Color.white);
    cMagnetMouse.setOpaque(false);
    pMagnet.xyPosition(pMagnet, cMagnetMouse, 1, 9, 1);
    cMagnetMouse.addItemListener(new Controler(MAGNET_MOUSE));
    cMagnetMouse.setToolTipText("Magnet mouse pointer");

    return pMagnet;
  }
  /**
   * Pour la gestion des actions, un controleur est associé à chaque composant
   */
  class Controler implements ActionListener, ItemListener, ChangeListener {//, KeyListener {

    int controlValue = 0;
    JComponent component;
    double defaultValueDouble;
    long defaultValueLong;
    int defaultValueInt;

    Controler(int controlValue) {
      this.controlValue = controlValue;
    }

    Controler(int controlValue, JComponent c, int defaultValueInt) {
      this(controlValue);
      this.component = c;
      this.defaultValueInt = defaultValueInt;
    }

    Controler(int controlValue, JComponent c, double defaultValueDouble) {
      this(controlValue);
      this.component = c;
      this.defaultValueDouble = defaultValueDouble;
    }

    Controler(int controlValue, JComponent c, long defaultValueLong) {
      this(controlValue);
      this.component = c;
      this.defaultValueLong = defaultValueLong;
    }

    public void actionPerformed(ActionEvent e) {
      switch(controlValue) {
        case FORMATTER: lgv.initFormatterHBLattice(fitScreen, optimizer); break;
        case ZOOM_PLUS: lgv.ZP(); break;
        case ZOOM_MOINS: lgv.ZM(); break;
        case TENSION: modTension(); break;
        case REPULSION: modRepulsion(); break;
        case TIME_SLEEP: modTimeSleep(); break;
        //case STEP: modStep(); break;
        default: break;
      }
    }// fin actionPerformed

// Implements ItemListener
    public void itemStateChanged(ItemEvent e) {
      switch(controlValue) {
        case FIT_SCREEN : fitScreen = ! fitScreen ; break; // JCheckBox
        case OPTIMIZE : optimizer = ! optimizer; break; // JCheckBox
        case MAGNET : getMagneto().setMagnet(! getMagneto().getMagnet()); break; // JCheckBox
        case FIX_FIRST_LEVEL : getMagneto().setFixFirstLevel(! getMagneto().fixFirstLevel()); break;
        case FIX_LAST_LEVEL : getMagneto().setFixLastLevel(! getMagneto().fixLastLevel()); break;
          //case FIX_BOTTOM : getMagneto().setFixBottom(! getMagneto().fixBottom()); break;
        case MAGNET_RELATIONS : getMagneto().setMagnetRelation(! getMagneto().magnetRelation()); break;
        case MAGNET_MOUSE : getMagneto().setMagnetMouse(! getMagneto().magnetMouse()); break;
        case THREE_D : lgv.setThreeD(! lgv.getThreeD()); break;
        //case ROTATION : getMagneto().setRotation(! getMagneto().getRotation()); break;
      }
    }// Fin itemStatechanged

// Implement KeyListener
/*          public void keyReleased(KeyEvent e) {;}
          public void keyPressed(KeyEvent e) {;}
          public void keyTyped(KeyEvent e) {
            System.out.println("Key Pressed");
              if(e.getKeyCode() == KeyEvent.VK_ENTER) {
                switch(controlValue) {
                  case TENSION: modTension(); break;
                  case REPULSION: modRepulsion(); break;
                }
            }
          }
*/
    public void modTension() {
      String rep = ((JTextField) component).getText();
      double d = 0.0;
      try {
        d = new Double(rep).doubleValue();
        getMagneto().setTensionFactor(d);
        st.setValue((int) (d*10));
      } catch(Exception e) {
        System.out.println("Valeur de répulsion non valide : "+rep);
        ((JTextField) component).setText(new Double(defaultValueDouble).toString());
        st.setValue((int) defaultValueDouble);
      }

    }

    /**
     * Méthode appelée lorsqu'un évenement sur le slide répulsion survient
     * Le composant passé en param?tre du controleur est le TextField
     */
    public void modSlideTension(int val) {
      ((JTextField) component).setText(new Integer(val/10).toString());
      modTension();
    }


          /*public void modRepulsion() {
            String rep = ((JTextField) component).getText();
    //System.out.println("Repulsion changed : "+rep);
            double d = 0.0;
            try {
              d = new Double(rep).doubleValue();
              getMagneto().setRepulsionFactor(d);
            } catch(Exception e) {
                System.out.println("Valeur de répulsion non valide : "+rep);
                ((JTextField) component).setText(new Double(defaultValueDouble).toString());
              }

          }*/

          /**
           * Modification de la répulsion
           */
    public void modRepulsion() {
      String rep = ((JTextField) component).getText();
      double d = 0;
      try {
        d = new Double(rep).doubleValue();
        getMagneto().setRepulsionFactor(((double) d)/10.0);
        sr.setValue((int) (d*10));
      } catch(Exception e) {
        System.out.println("Valeur de répulsion non valide : "+rep);
        Double dou = new Double( ((double) defaultValueDouble)*10.0);
        ((JTextField) component).setText(dou.toString());
        sr.setValue((int) (defaultValueDouble*10));
      }
    }

    /**
     * Méthode appelée lorsqu'un évenement sur le slide répulsion survient
     * Le composant passé en param?tre du controleur est le TextField
     */
    public void modSlideRepulsion(int val) {
      ((JTextField) component).setText(new Integer(val/10).toString());
      modRepulsion();
    }

    public void modTimeSleep() {
      String rep = ((JTextField) component).getText();
      //System.out.println("Repulsion changed : "+rep);
      long d;
      try {
        d = new Long(rep).longValue();
        getMagneto().setTimeSleep(d);
      } catch(Exception e) {
        System.out.println("Valeur de répulsion non valide : "+rep);
        ((JTextField) component).setText(new Long(defaultValueLong).toString());
      }
    }

    public void modeSlideTime(int val) {
      ((JTextField) component).setText(new Integer(val).toString());
      modTimeSleep();
    }

    public void modeSlideRotation(int val) {
      getMagneto().setRotation(((float) (val-10))/2f);
    }

 /*   public void modStep() {
      String rep = ((JTextField) component).getText();
      //System.out.println("Repulsion changed : "+rep);
      int d;
      try {
        d = new Integer(rep).intValue();
        getMagneto().setPas(d);
      } catch(Exception e) {
        System.out.println("Valeur de step non valide : "+rep);
        ((JTextField) component).setText(new Integer(defaultValueInt).toString());
      }
    }
*/
    public void stateChanged(ChangeEvent e) {
      int v = ((JSlider) e.getSource()).getValue();
      switch(controlValue) {
        case REPULSION_SLIDE : modSlideRepulsion(v) ; break; // JSlide
        case TENSION_SLIDE : modSlideTension(v) ; break; // JSlide
        case TIME_SLIDE : modeSlideTime(v); break; // JSlide time
        case ROTATION : modeSlideRotation(v); break; // JSlide rotation (3D mode)
      }
    }

  }// Fin controleur

}