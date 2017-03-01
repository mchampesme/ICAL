/*
 *  Copyright LIPN
 *  contributor(s) : Marc Champesme (2006) marc.champesme@lipn.univ-paris13.fr
 *  
 *  This software is a computer program whose purpose is the Incremental construction of Alpha lattices.
 *  
 *  This software is governed by the CeCILL license under French law and
 *  abiding by the rules of distribution of free software.  You can  use, 
 *  modify and/ or redistribute the software under the terms of the CeCILL
 *  license as circulated by CEA, CNRS and INRIA at the following URL
 *  "http://www.cecill.info". 
 *  
 *  As a counterpart to the access to the source code and  rights to copy,
 *  modify and redistribute granted by the license, users are provided only
 *  with a limited warranty  and the software's author,  the holder of the
 *  economic rights,  and the successive licensors  have only  limited
 *  liability. 
 *  
 *  In this respect, the user's attention is drawn to the risks associated
 *  with loading,  using,  modifying and/or developing or reproducing the
 *  software by the user in light of its specific status of free software,
 *  that may mean  that it is complicated to manipulate,  and  that  also
 *  therefore means  that it is reserved for developers  and  experienced
 *  professionals having in-depth computer knowledge. Users are therefore
 *  encouraged to load and test the software's suitability as regards their
 *  requirements in conditions enabling the security of their systems and/or 
 *  data to be ensured and,  more generally, to use and operate it in the 
 *  same conditions as regards security. 
 *  
 *  The fact that you are presently reading this means that you have had
 *  knowledge of the CeCILL license and that you accept its terms.
 */
package lattice.alpha.gui.view;

import javax.swing.BorderFactory;
import javax.swing.JFormattedTextField;
import javax.swing.JLabel;
import javax.swing.JPanel;

import java.awt.BorderLayout;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.text.NumberFormat;

public class PercentTextFieldPanel extends JPanel {
    /**
     * 
     */
    private static final long serialVersionUID = 9209922056453758365L;

    private JLabel valueLabel;

    private String valueString;

    private JFormattedTextField valueField;

    private NumberFormat percentFormat;

    public PercentTextFieldPanel(String valueStr, double initValue) {
        super(new BorderLayout());

        valueString = valueStr;
        percentFormat = NumberFormat.getPercentInstance();

        // Create the label
        valueLabel = new JLabel(valueString);

        // Create the text field and set it up
        valueField = new JFormattedTextField(percentFormat);
        valueField.setValue(new Double(initValue));
        valueField.setColumns(5);
        valueLabel.setLabelFor(valueField);

        JPanel labelPane = new JPanel();
        labelPane.add(valueLabel);
        JPanel fieldPane = new JPanel();
        fieldPane.add(valueField);

        setBorder(BorderFactory.createEmptyBorder(20, 20, 20, 20));
        add(labelPane, BorderLayout.CENTER);
        add(fieldPane, BorderLayout.LINE_END);
    }

    public void  addValueChangeListener(PropertyChangeListener listener) {
        valueField.addPropertyChangeListener("value", listener);
    }
    
    public boolean isSourceOfPropertyChange(PropertyChangeEvent e) {
        return e.getSource() == valueField;
    }

    public double getValue() {
        return ((Number) valueField.getValue()).doubleValue();
    }
}
