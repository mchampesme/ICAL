/*
 * **********************************************************************
 * Copyright (C) 2004 The Galicia Team Modifications to the initial code base
 * are copyright of their respective authors, or their employers as appropriate.
 * Authorship of the modifications may be determined from the ChangeLog placed
 * at the end of this file. This program is free software; you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of the
 * License, or (at your option) any later version. This program is distributed
 * in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even
 * the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details. You should have
 * received a copy of the GNU Lesser General Public License along with this
 * program; if not, write to the Free Software Foundation, Inc., 59 Temple
 * Place, Suite 330, Boston, MA 02111-1307 USA; or visit the following url:
 * http://www.gnu.org/copyleft/lesser.html
 * **********************************************************************
 */

package lattice.gui;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import javax.swing.UIManager;

import lattice.gui.filter.AbstractFilter;
import lattice.gui.filter.IBM_Filter;
import lattice.gui.filter.Krss_Filter;
import lattice.gui.filter.MVC_Filter;
import lattice.gui.filter.RCF_Filter;
import lattice.gui.filter.SLF_Filter;
import lattice.gui.filter.XML_Filter;
import lattice.io.AbstractReader;
import lattice.io.AbstractWriter;
import lattice.io.IbmReader;
import lattice.io.IbmWriter;
import lattice.io.RcfReader;
import lattice.io.RcfWriter;
import lattice.io.SlfReader;
import lattice.io.SlfWriter;
import lattice.io.XmlReader;
import lattice.io.XmlWriter;
import lattice.io.task.ReadingTask;
import lattice.io.task.WritingTask;
import lattice.util.relation.RelationalContextFamily;

/**
 * @author Mr ROUME To change this generated comment edit the template variable
 *         "typecomment": Window>Preferences>Java>Templates. To enable and
 *         disable the creation of type comments go to
 *         Window>Preferences>Java>Code Generation.
 */
public abstract class OpenFileFrame extends ConsoleFrame {

    private static File lastDirectory = null;

    public static int BINARY_DATA = 0;

    public static int MULTI_VALUE_DATA = 1;

    public static int FAMILY_DATA = 2;

    public static int LATTICE_DATA = 3;

    public static int OBJECTS_DATA = 4;

    public static int ATTRIBUTES_DATA = 5;

    public static int KRSS_DATA = 6;

    private static RCF_Filter rcfFilter = new RCF_Filter();

    private static IBM_Filter ibmFilter = new IBM_Filter();

    private static SLF_Filter slfFilter = new SLF_Filter();

    private static XML_Filter xmlBinFilter = new XML_Filter(".bin");

    private static XML_Filter xmlMvcFilter = new XML_Filter(".mvc");

    private static XML_Filter xmlRcfFilter = new XML_Filter(".rcf");

    private static XML_Filter xmlLatFilter = new XML_Filter(".lat");

    private static Krss_Filter krssFilter = new Krss_Filter();

    private static MVC_Filter mvcFilter = new MVC_Filter();

    protected ReadingTask readTask = null;

    protected WritingTask writeTask = null;

    // protected WritingTask writeTask=null;

    /**
     * Constructor for OpenFileFrame.
     */
    public OpenFileFrame() {
        super();
    }

    /**
     * Constructor for OpenFileFrame.
     */
    public OpenFileFrame(String title) {
        super();
        setTitle(title);
    }

    /**
     * Constructor for OpenFileFrame.
     * 
     * @param div_loc
     */
    public OpenFileFrame(double div_loc) {
        super(div_loc);
    }

    private JFileChooser getFileChooser(int chooserAction) {
        JFileChooser fileChooser = null;
        if (lastDirectory == null)
            fileChooser = new JFileChooser();
        else
            fileChooser = new JFileChooser(lastDirectory);

        fileChooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
        fileChooser.setDialogType(chooserAction);
        fileChooser.setMultiSelectionEnabled(false);
        // fileChooser.getTreeLock();
        UIManager.installLookAndFeel(UIManager.getSystemLookAndFeelClassName(),
                                     "JFileChooser");
        return fileChooser;

    }

    private File selectedFile(JFileChooser fileChooser, int chooserAction) {
        File fich = null;

        int result = JFileChooser.CANCEL_OPTION;

        do {
            if (chooserAction == JFileChooser.OPEN_DIALOG)
                result = fileChooser.showOpenDialog(this);
            if (chooserAction == JFileChooser.SAVE_DIALOG)
                result = fileChooser.showSaveDialog(this);
            if (result == JFileChooser.CANCEL_OPTION
                || fileChooser.getSelectedFile() == null) {
                return null;
            }
            if (fileChooser.getFileFilter() == fileChooser
                    .getChoosableFileFilters()[0]) {
                // Si le filtre de selection est * alors on cherche s'il existe
                // un filtre qui match le fichi� choisit
                for (int i = 1; i < fileChooser.getChoosableFileFilters().length
                                && fich == null; i++) {
                    if (fileChooser.getChoosableFileFilters()[i]
                            .accept(fileChooser.getSelectedFile())) {
                        fileChooser.setFileFilter(fileChooser
                                .getChoosableFileFilters()[i]);
                        lastDirectory = fileChooser.getCurrentDirectory();
                        fich = fileChooser.getSelectedFile();
                    }
                }
                if (fich == null)
                    // Aucun filtre n'a pu match� le fichi� s�lectionn�
                    JOptionPane
                            .showMessageDialog(this,
                                               "The selected file has no known file extention!");

            } else {
                // Un filtre est s�l�ctionn� et il est different de *
                lastDirectory = fileChooser.getCurrentDirectory();
                if (!fileChooser
                        .getSelectedFile()
                        .getName()
                        .endsWith(
                                  ((AbstractFilter) fileChooser.getFileFilter())
                                          .getFileExtension()))
                    // Si le fichier choisit ne poss�de pas la bonne extension,
                    // on lui met automatiquement
                    // Ceci ne sert que lorsque l'on choisit un fichier de
                    // sauvegarde
                    fich = new File(lastDirectory,
                                    fileChooser.getSelectedFile().getName()
                                            + ((AbstractFilter) fileChooser
                                                    .getFileFilter())
                                                    .getFileExtension());
                else
                    fich = fileChooser.getSelectedFile();
            }
        } while (fich == null);
        return fich;
    }

    protected File getFileFor(int chooserAction, int dataType) {
        /*
         * le removeChoosableFileFilter est comment� car sous MacOS cela plante !
         */
        JFileChooser fileChooser = getFileChooser(chooserAction);
        switch (dataType) {
            case 0:

                // initialiser le JFileChooser
                fileChooser.addChoosableFileFilter(slfFilter);
                fileChooser.addChoosableFileFilter(ibmFilter);
                fileChooser.addChoosableFileFilter(xmlBinFilter);
                // fileChooser.removeChoosableFileFilter(fileChooser.getChoosableFileFilters()[0]);
                // pour que soit s�lectionn� le filefilter g�n�rique par d�faut
                fileChooser
                        .setFileFilter(fileChooser.getChoosableFileFilters()[0]);
                break;

            case 1:

                // initialiser le JFileChooser
                fileChooser.addChoosableFileFilter(mvcFilter);
                fileChooser.addChoosableFileFilter(xmlMvcFilter);
                // fileChooser.removeChoosableFileFilter(fileChooser.getChoosableFileFilters()[0]);
                // pour que soit s�lectionn� le filefilter g�n�rique par d�faut
                fileChooser
                        .setFileFilter(fileChooser.getChoosableFileFilters()[0]);
                break;

            case 2:

                // initialiser le JFileChooser
                fileChooser.addChoosableFileFilter(rcfFilter);
                fileChooser.addChoosableFileFilter(xmlRcfFilter);
                // fileChooser.removeChoosableFileFilter(fileChooser.getChoosableFileFilters()[0]);
                // pour que soit s�lectionn� le filefilter g�n�rique par d�faut
                fileChooser
                        .setFileFilter(fileChooser.getChoosableFileFilters()[0]);
                break;

            case 3:

                // initialiser le JFileChooser
                fileChooser.addChoosableFileFilter(xmlLatFilter);
                // fileChooser.addChoosableFileFilter(pdfFilter);
                // fileChooser.removeChoosableFileFilter(fileChooser.getChoosableFileFilters()[0]);
                // pour que soit s�lectionn� le filefilter g�n�rique par d�faut
                fileChooser
                        .setFileFilter(fileChooser.getChoosableFileFilters()[0]);
                break;

            case 6:
                fileChooser.addChoosableFileFilter(krssFilter);
                fileChooser
                        .setFileFilter(fileChooser.getChoosableFileFilters()[0]);
                break;

            default:
                break;
        }

        return selectedFile(fileChooser, chooserAction);

    }

    protected AbstractReader getReaderFromFile(File file)
                                                         throws FileNotFoundException {
        if (rcfFilter.accept(file))
            return new RcfReader(new FileReader(file));
        if (ibmFilter.accept(file))
            return new IbmReader(new FileReader(file));
        if (slfFilter.accept(file))
            return new SlfReader(new FileReader(file));
        if (xmlBinFilter.accept(file) || xmlMvcFilter.accept(file)
            || xmlRcfFilter.accept(file) || xmlLatFilter.accept(file))
            return new XmlReader(new FileReader(file));
        return null;
    }

    protected AbstractWriter getWriterFromFile(File file) throws IOException {
        if (rcfFilter.accept(file))
            return new RcfWriter(new FileWriter(file));
        if (ibmFilter.accept(file))
            return new IbmWriter(new FileWriter(file));
        if (slfFilter.accept(file))
            return new SlfWriter(new FileWriter(file));
        if (xmlBinFilter.accept(file) || xmlMvcFilter.accept(file)
            || xmlRcfFilter.accept(file) || xmlLatFilter.accept(file))
            return new XmlWriter(new FileWriter(file));
        return null;
    }

    protected void writeAction(Object data, String actionType, int writingType) {
        File fich = null;
        fich = getFileFor(JFileChooser.SAVE_DIALOG, writingType);
        if (fich == null) {
            addMessage("File not selected...");
            addMessage(actionType + " Cancelled!\n");
            return;
        }

        AbstractWriter writer = null;
        try {
            writer = getWriterFromFile(fich);
        } catch (FileNotFoundException fnfe) {
            addMessage("File Not Found!");
            addMessage("Writing Aborted...\n");
            return;
        } catch (IOException ioe) {
            ioe.printStackTrace();
            addMessage(ioe.getMessage());
            addMessage("Writing Aborted...\n");
            return;
        }
        if (writer == null) {
            addMessage("Can not find any writer for the file!");
            addMessage("Writing Aborted...\n");
        }
        writer.setData(data);
        // Etant donn�e que le XmlReader peux servir a plusieur actions, il faut
        // lui pr�cis� ce que l'on attend
        if (writer instanceof XmlWriter)
            ((XmlWriter) writer).setTypeOfWriting(writingType);
        writeTask.setDataWriter(writer);
        writeTask.exec();

    }

    protected void readAction(String actionType, int readingType) {
        File fich = null;
        fich = getFileFor(JFileChooser.OPEN_DIALOG, readingType);
        if (fich == null) {
            addMessage("File not selected...");
            addMessage(actionType + " Cancelled!\n");
            return;
        }

        AbstractReader reader = null;
        try {
            reader = getReaderFromFile(fich);
            reader.setDefaultNameForData(fich.getName());
        } catch (FileNotFoundException fnfe) {
            addMessage("File Not Found!");
            addMessage("Reading Aborted...\n");
            return;
        }

        addMessage("File found, reader ready\n");
        
        if (reader instanceof XmlReader)
            ((XmlReader) reader).setTypeOfReading(readingType);
        readTask.setDataReader(reader);
        readTask.exec();
    }

    protected void openData() {
        addMessage("Open...");

        int readingType = whichData("Open data from:");
        if (readingType == -1) {
            addMessage("Open Cancelled!\n");
            return;
        }
        readAction("Open", readingType);
    }

    protected void importData() {
        addMessage("Import...");

        int readingType = whichData("Import data from:");
        if (readingType == -1) {
            addMessage("Import Cancelled!\n");
            return;
        }
        readAction("Import", readingType);
    }

    // abstract void exportData();

    protected void saveAllData(RelationalContextFamily data) {
        addMessage("Save all...");
        writeAction(data, "Save all", FAMILY_DATA);
    }

    public int whichData(String action) {
        String action1 = action + " Relational Context Family";
        String action2 = action + " Binary Context";
        String action3 = action + " Multi-Valued Context";
        String action4 = action + " Lattice";
        String action5 = action + " Racer";

        Object[] lesVals = { action1, action2, action3, action4 };
        String val = (String) JOptionPane
                .showInputDialog(this, "Choose an action :",
                                 "Choose an action :",
                                 JOptionPane.QUESTION_MESSAGE, null, lesVals,
                                 action1);
        if (val == null)
            return -1;
        if (val.equals(action1))
            return FAMILY_DATA;
        if (val.equals(action2))
            return BINARY_DATA;
        if (val.equals(action3))
            return MULTI_VALUE_DATA;
        if (val.equals(action4))
            return LATTICE_DATA;
        if (val.equals(action5))
            return KRSS_DATA;
        return -1;
    }

    public File chooseSaveConsoleFile() {
        File fich = null;
        JFileChooser fileChooser = new JFileChooser();
        int result = fileChooser.showSaveDialog(this);
        if (result == JFileChooser.CANCEL_OPTION
            || fileChooser.getSelectedFile() == null)
            return null;
        else {
            fich = fileChooser.getSelectedFile();
            lastDirectory = fileChooser.getCurrentDirectory();
        }
        return fich;
    }

}
