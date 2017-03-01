<?xml version = '1.0' encoding = 'ISO-8859-1'?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/TR/WD-xsl">

<xsl:template match="/">
  <HTML>
	<HEAD>
        	<TITLE>Regles</TITLE>
		<STYLE>

		<!-- =========================================================== -->
		<!-- Le style utilisé pour les titres                            -->                                                                                                                                                                                                  
		<!-- =========================================================== -->

			H1 {
    			font-size: 24pt;
    			color: blue;
    			text-align:center; letter-spacing:8px;
        		font-weight:bold;
			font-family:Comic Sans MS; 
  			}

  			H2 {
    			font-size: 14pt;
    			font-weight: bold;
   			color: green;
    			text-align:left; letter-spacing:8px;
   			font-family: Comic Sans MS;
  			}
			H3 {
			font-family:font-family:Tahoma,Arial,sans-serif; 
    			font-size: 9pt;
  			}
	
		</STYLE>
      	</HEAD>
    	<BODY>
        <h1>Approximative Rule Basis</h1>
      		
		<br><h2>1. Features</h2></br>

		<br><xsl:apply-templates select="//caracteristiques/base_donnees" /></br>
	

		<br><xsl:apply-templates select="//caracteristiques/support_minimal" /></br>
		
       		<br><xsl:apply-templates select="//caracteristiques/confiance_minimale" /></br>
		
		<br><h2>2. Approximative Rule Basis </h2></br>
		
		<br><xsl:apply-templates select="//ensemble_regles/nombre_regles" /></br>

		<hr/>
      		<TABLE WIDTH="100%" CELLPADDING="5">
        		<h3><xsl:apply-templates select="//ensemble_regles/regle" /></h3>
      		</TABLE>
    	</BODY>
  </HTML>
</xsl:template>


<!-- ================================================================== -->
<!-- 1) La section caractéristiques                                     -->                                                                                                                                                                                                  
<!-- ================================================================== -->


<!-- ================================================================== -->
<!-- 1.1 nom dela base de données                                       -->                                                                                                                                                                                                  
<!-- ================================================================== -->

<xsl:template match="base_donnees">
   <b>Dataset :</b> <xsl:value-of select="." />
</xsl:template>

<!-- ================================================================== -->
<!-- 1.2 support de l'usager                                            -->                                                                                                                                                                                                  
<!-- ================================================================== -->

<xsl:template match="support_minimal">
   <b><i>Minimum support </i>:</b> <xsl:value-of select="." />
</xsl:template>

<!-- ================================================================== -->
<!-- 1.3 confiance de l'usager                                          -->                                                                                                                                                                                                  
<!-- ================================================================== -->

<xsl:template match="confiance_minimale">
   <b><i>Minimum confidence</i>:</b> <xsl:value-of select="." />
</xsl:template>


<!-- ================================================================== -->
<!-- 2) La section ensemble_règles                                      -->                                                                                                                                                         
<!-- ================================================================== -->

<!-- ================================================================== -->
<!-- 2.1 nombre de règles de la base                                    -->                                                                                                                                                                                                  
<!-- ================================================================== -->

<xsl:template match="nombre_regles">
   <p> The basis has <b><xsl:value-of select="." /></b> rules.</p>
</xsl:template>

<!-- ================================================================== -->
<!-- 2.2 ensemble des règles                                            -->                                                                                                                                                                                                  
<!-- ================================================================== -->

<xsl:template match="regle">
  <TR>
    <xsl:apply-templates select="antecedent" />
    <xsl:apply-templates select="consequence" />
    <xsl:apply-templates select="support" />
    <xsl:apply-templates select="confiance" />
  </TR>
  <TR><TD COLSPAN="4"><HR /></TD></TR>
</xsl:template>

<!-- ================================================================== -->
<!-- 2.2.1  antécédent                                                  -->                                                                                                                                                                                                  
<!-- ================================================================== -->

<xsl:template match="antecedent">
  <TD>
    <b>premise</b> = {<xsl:value-of select="." />}
  </TD>
</xsl:template>

<!-- ================================================================== -->
<!-- 2.2.1  conséquence                                                 -->                                                                                                                                                                                                  
<!-- ================================================================== -->

<xsl:template match="consequence">
  <TD>
     <b>consequence</b> = {<xsl:value-of select="." />}
  </TD>
</xsl:template>

<!-- ================================================================== -->
<!-- 2.2.1  support                                                     -->                                                                                                                                                                                                  
<!-- ================================================================== -->

<xsl:template match="support">
  <TD>
    <b>support =</b> <xsl:value-of select="." />
  </TD>
</xsl:template>

<!-- ================================================================== -->
<!-- 2.2.1  confiance                                                   -->                                                                                                                                                                                                  
<!-- ================================================================== -->

<xsl:template match="confiance">
  <TD>
    <b>confidence =</b> <xsl:value-of select="." />
  </TD>
</xsl:template>

</xsl:stylesheet>