/*
 * Created on 2004-11-30
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package lattice.gui.filter;

/**
 * @author rouanehm
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class Krss_Filter extends AbstractFilter {

	  /**
	   * Obtient le nom du type de format
	   * @return une String contenant le nom du format sélectionné
	   */
	  public String getDescription()
	  {
	    return "Knowledge base defintion (ascii): *"+getFileExtension();
	  }

	  public String getFileExtension(){
		  return ".krss";
	  }

}
