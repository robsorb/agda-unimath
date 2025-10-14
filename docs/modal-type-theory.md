# Modal type theory

<pre class="Agda"><a id="30" class="Symbol">{-#</a> <a id="34" class="Keyword">OPTIONS</a> <a id="42" class="Pragma">--cohesion</a> <a id="53" class="Pragma">--flat-split</a> <a id="66" class="Symbol">#-}</a>
</pre>
Modal type theory is the study of type theory extended with syntactic _modal_
operators. These are operations on types that increase the expressivity of the
type theory in some way.

In this namespace, we consider modal extensions of Martin-Löf type theory with a
[flat modality](modal-type-theory.flat-modality.md) `♭`,
[sharp modality](modal-type-theory.sharp-modality.md) `♯`, and more to come. The
[adjoint pair of modalities](modal-type-theory.flat-sharp-adjunction.md)
`♭ ⊣ ＃` display a structure on all types referred to as _spatial_, or
_cohesive_ structure.

- To read more, continue to [crisp types](modal-type-theory.crisp-types.md).

## Modules in the modal type theory namespace

<pre class="Agda"><a id="776" class="Keyword">module</a> <a id="783" href="modal-type-theory.html" class="Module">modal-type-theory</a> <a id="801" class="Keyword">where</a>

<a id="808" class="Keyword">open</a> <a id="813" class="Keyword">import</a> <a id="820" href="modal-type-theory.action-on-homotopies-flat-modality.html" class="Module">modal-type-theory.action-on-homotopies-flat-modality</a> <a id="873" class="Keyword">public</a>
<a id="880" class="Keyword">open</a> <a id="885" class="Keyword">import</a> <a id="892" href="modal-type-theory.action-on-identifications-crisp-functions.html" class="Module">modal-type-theory.action-on-identifications-crisp-functions</a> <a id="952" class="Keyword">public</a>
<a id="959" class="Keyword">open</a> <a id="964" class="Keyword">import</a> <a id="971" href="modal-type-theory.action-on-identifications-flat-modality.html" class="Module">modal-type-theory.action-on-identifications-flat-modality</a> <a id="1029" class="Keyword">public</a>
<a id="1036" class="Keyword">open</a> <a id="1041" class="Keyword">import</a> <a id="1048" href="modal-type-theory.crisp-cartesian-product-types.html" class="Module">modal-type-theory.crisp-cartesian-product-types</a> <a id="1096" class="Keyword">public</a>
<a id="1103" class="Keyword">open</a> <a id="1108" class="Keyword">import</a> <a id="1115" href="modal-type-theory.crisp-coproduct-types.html" class="Module">modal-type-theory.crisp-coproduct-types</a> <a id="1155" class="Keyword">public</a>
<a id="1162" class="Keyword">open</a> <a id="1167" class="Keyword">import</a> <a id="1174" href="modal-type-theory.crisp-dependent-function-types.html" class="Module">modal-type-theory.crisp-dependent-function-types</a> <a id="1223" class="Keyword">public</a>
<a id="1230" class="Keyword">open</a> <a id="1235" class="Keyword">import</a> <a id="1242" href="modal-type-theory.crisp-dependent-pair-types.html" class="Module">modal-type-theory.crisp-dependent-pair-types</a> <a id="1287" class="Keyword">public</a>
<a id="1294" class="Keyword">open</a> <a id="1299" class="Keyword">import</a> <a id="1306" href="modal-type-theory.crisp-function-types.html" class="Module">modal-type-theory.crisp-function-types</a> <a id="1345" class="Keyword">public</a>
<a id="1352" class="Keyword">open</a> <a id="1357" class="Keyword">import</a> <a id="1364" href="modal-type-theory.crisp-identity-types.html" class="Module">modal-type-theory.crisp-identity-types</a> <a id="1403" class="Keyword">public</a>
<a id="1410" class="Keyword">open</a> <a id="1415" class="Keyword">import</a> <a id="1422" href="modal-type-theory.crisp-law-of-excluded-middle.html" class="Module">modal-type-theory.crisp-law-of-excluded-middle</a> <a id="1469" class="Keyword">public</a>
<a id="1476" class="Keyword">open</a> <a id="1481" class="Keyword">import</a> <a id="1488" href="modal-type-theory.crisp-pullbacks.html" class="Module">modal-type-theory.crisp-pullbacks</a> <a id="1522" class="Keyword">public</a>
<a id="1529" class="Keyword">open</a> <a id="1534" class="Keyword">import</a> <a id="1541" href="modal-type-theory.crisp-types.html" class="Module">modal-type-theory.crisp-types</a> <a id="1571" class="Keyword">public</a>
<a id="1578" class="Keyword">open</a> <a id="1583" class="Keyword">import</a> <a id="1590" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html" class="Module">modal-type-theory.dependent-universal-property-flat-discrete-crisp-types</a> <a id="1663" class="Keyword">public</a>
<a id="1670" class="Keyword">open</a> <a id="1675" class="Keyword">import</a> <a id="1682" href="modal-type-theory.flat-discrete-crisp-types.html" class="Module">modal-type-theory.flat-discrete-crisp-types</a> <a id="1726" class="Keyword">public</a>
<a id="1733" class="Keyword">open</a> <a id="1738" class="Keyword">import</a> <a id="1745" href="modal-type-theory.flat-modality.html" class="Module">modal-type-theory.flat-modality</a> <a id="1777" class="Keyword">public</a>
<a id="1784" class="Keyword">open</a> <a id="1789" class="Keyword">import</a> <a id="1796" href="modal-type-theory.flat-sharp-adjunction.html" class="Module">modal-type-theory.flat-sharp-adjunction</a> <a id="1836" class="Keyword">public</a>
<a id="1843" class="Keyword">open</a> <a id="1848" class="Keyword">import</a> <a id="1855" href="modal-type-theory.functoriality-flat-modality.html" class="Module">modal-type-theory.functoriality-flat-modality</a> <a id="1901" class="Keyword">public</a>
<a id="1908" class="Keyword">open</a> <a id="1913" class="Keyword">import</a> <a id="1920" href="modal-type-theory.functoriality-sharp-modality.html" class="Module">modal-type-theory.functoriality-sharp-modality</a> <a id="1967" class="Keyword">public</a>
<a id="1974" class="Keyword">open</a> <a id="1979" class="Keyword">import</a> <a id="1986" href="modal-type-theory.sharp-codiscrete-maps.html" class="Module">modal-type-theory.sharp-codiscrete-maps</a> <a id="2026" class="Keyword">public</a>
<a id="2033" class="Keyword">open</a> <a id="2038" class="Keyword">import</a> <a id="2045" href="modal-type-theory.sharp-codiscrete-types.html" class="Module">modal-type-theory.sharp-codiscrete-types</a> <a id="2086" class="Keyword">public</a>
<a id="2093" class="Keyword">open</a> <a id="2098" class="Keyword">import</a> <a id="2105" href="modal-type-theory.sharp-modality.html" class="Module">modal-type-theory.sharp-modality</a> <a id="2138" class="Keyword">public</a>
<a id="2145" class="Keyword">open</a> <a id="2150" class="Keyword">import</a> <a id="2157" href="modal-type-theory.transport-along-crisp-identifications.html" class="Module">modal-type-theory.transport-along-crisp-identifications</a> <a id="2213" class="Keyword">public</a>
<a id="2220" class="Keyword">open</a> <a id="2225" class="Keyword">import</a> <a id="2232" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html" class="Module">modal-type-theory.universal-property-flat-discrete-crisp-types</a> <a id="2295" class="Keyword">public</a>
</pre>