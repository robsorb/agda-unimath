# Logic

## Modules in the logic namespace

<pre class="Agda"><a id="53" class="Keyword">module</a> <a id="60" href="logic.html" class="Module">logic</a> <a id="66" class="Keyword">where</a>

<a id="73" class="Keyword">open</a> <a id="78" class="Keyword">import</a> <a id="85" href="logic.complements-de-morgan-subtypes.html" class="Module">logic.complements-de-morgan-subtypes</a> <a id="122" class="Keyword">public</a>
<a id="129" class="Keyword">open</a> <a id="134" class="Keyword">import</a> <a id="141" href="logic.complements-decidable-subtypes.html" class="Module">logic.complements-decidable-subtypes</a> <a id="178" class="Keyword">public</a>
<a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="logic.complements-double-negation-stable-subtypes.html" class="Module">logic.complements-double-negation-stable-subtypes</a> <a id="247" class="Keyword">public</a>
<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="logic.de-morgan-embeddings.html" class="Module">logic.de-morgan-embeddings</a> <a id="293" class="Keyword">public</a>
<a id="300" class="Keyword">open</a> <a id="305" class="Keyword">import</a> <a id="312" href="logic.de-morgan-maps.html" class="Module">logic.de-morgan-maps</a> <a id="333" class="Keyword">public</a>
<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="logic.de-morgan-propositions.html" class="Module">logic.de-morgan-propositions</a> <a id="381" class="Keyword">public</a>
<a id="388" class="Keyword">open</a> <a id="393" class="Keyword">import</a> <a id="400" href="logic.de-morgan-subtypes.html" class="Module">logic.de-morgan-subtypes</a> <a id="425" class="Keyword">public</a>
<a id="432" class="Keyword">open</a> <a id="437" class="Keyword">import</a> <a id="444" href="logic.de-morgan-types.html" class="Module">logic.de-morgan-types</a> <a id="466" class="Keyword">public</a>
<a id="473" class="Keyword">open</a> <a id="478" class="Keyword">import</a> <a id="485" href="logic.de-morgans-law.html" class="Module">logic.de-morgans-law</a> <a id="506" class="Keyword">public</a>
<a id="513" class="Keyword">open</a> <a id="518" class="Keyword">import</a> <a id="525" href="logic.dirk-gentlys-principle.html" class="Module">logic.dirk-gentlys-principle</a> <a id="554" class="Keyword">public</a>
<a id="561" class="Keyword">open</a> <a id="566" class="Keyword">import</a> <a id="573" href="logic.double-negation-dense-maps.html" class="Module">logic.double-negation-dense-maps</a> <a id="606" class="Keyword">public</a>
<a id="613" class="Keyword">open</a> <a id="618" class="Keyword">import</a> <a id="625" href="logic.double-negation-dense-subtypes.html" class="Module">logic.double-negation-dense-subtypes</a> <a id="662" class="Keyword">public</a>
<a id="669" class="Keyword">open</a> <a id="674" class="Keyword">import</a> <a id="681" href="logic.double-negation-eliminating-maps.html" class="Module">logic.double-negation-eliminating-maps</a> <a id="720" class="Keyword">public</a>
<a id="727" class="Keyword">open</a> <a id="732" class="Keyword">import</a> <a id="739" href="logic.double-negation-elimination.html" class="Module">logic.double-negation-elimination</a> <a id="773" class="Keyword">public</a>
<a id="780" class="Keyword">open</a> <a id="785" class="Keyword">import</a> <a id="792" href="logic.double-negation-stable-embeddings.html" class="Module">logic.double-negation-stable-embeddings</a> <a id="832" class="Keyword">public</a>
<a id="839" class="Keyword">open</a> <a id="844" class="Keyword">import</a> <a id="851" href="logic.double-negation-stable-subtypes.html" class="Module">logic.double-negation-stable-subtypes</a> <a id="889" class="Keyword">public</a>
<a id="896" class="Keyword">open</a> <a id="901" class="Keyword">import</a> <a id="908" href="logic.functoriality-existential-quantification.html" class="Module">logic.functoriality-existential-quantification</a> <a id="955" class="Keyword">public</a>
<a id="962" class="Keyword">open</a> <a id="967" class="Keyword">import</a> <a id="974" href="logic.irrefutable-types.html" class="Module">logic.irrefutable-types</a> <a id="998" class="Keyword">public</a>
<a id="1005" class="Keyword">open</a> <a id="1010" class="Keyword">import</a> <a id="1017" href="logic.markovian-types.html" class="Module">logic.markovian-types</a> <a id="1039" class="Keyword">public</a>
<a id="1046" class="Keyword">open</a> <a id="1051" class="Keyword">import</a> <a id="1058" href="logic.markovs-principle.html" class="Module">logic.markovs-principle</a> <a id="1082" class="Keyword">public</a>
<a id="1089" class="Keyword">open</a> <a id="1094" class="Keyword">import</a> <a id="1101" href="logic.propositional-double-negation-elimination.html" class="Module">logic.propositional-double-negation-elimination</a> <a id="1149" class="Keyword">public</a>
<a id="1156" class="Keyword">open</a> <a id="1161" class="Keyword">import</a> <a id="1168" href="logic.propositionally-decidable-maps.html" class="Module">logic.propositionally-decidable-maps</a> <a id="1205" class="Keyword">public</a>
<a id="1212" class="Keyword">open</a> <a id="1217" class="Keyword">import</a> <a id="1224" href="logic.propositionally-decidable-types.html" class="Module">logic.propositionally-decidable-types</a> <a id="1262" class="Keyword">public</a>
<a id="1269" class="Keyword">open</a> <a id="1274" class="Keyword">import</a> <a id="1281" href="logic.propositionally-double-negation-eliminating-maps.html" class="Module">logic.propositionally-double-negation-eliminating-maps</a> <a id="1336" class="Keyword">public</a>
</pre>