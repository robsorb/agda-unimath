# Lists

## Modules in the lists namespace

<pre class="Agda"><a id="53" class="Keyword">module</a> <a id="60" href="lists.html" class="Module">lists</a> <a id="66" class="Keyword">where</a>

<a id="73" class="Keyword">open</a> <a id="78" class="Keyword">import</a> <a id="85" href="lists.arrays.html" class="Module">lists.arrays</a> <a id="98" class="Keyword">public</a>
<a id="105" class="Keyword">open</a> <a id="110" class="Keyword">import</a> <a id="117" href="lists.concatenation-lists.html" class="Module">lists.concatenation-lists</a> <a id="143" class="Keyword">public</a>
<a id="150" class="Keyword">open</a> <a id="155" class="Keyword">import</a> <a id="162" href="lists.concatenation-tuples.html" class="Module">lists.concatenation-tuples</a> <a id="189" class="Keyword">public</a>
<a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="lists.dependent-sequences.html" class="Module">lists.dependent-sequences</a> <a id="234" class="Keyword">public</a>
<a id="241" class="Keyword">open</a> <a id="246" class="Keyword">import</a> <a id="253" href="lists.equivalence-tuples-finite-sequences.html" class="Module">lists.equivalence-tuples-finite-sequences</a> <a id="295" class="Keyword">public</a>
<a id="302" class="Keyword">open</a> <a id="307" class="Keyword">import</a> <a id="314" href="lists.finite-sequences.html" class="Module">lists.finite-sequences</a> <a id="337" class="Keyword">public</a>
<a id="344" class="Keyword">open</a> <a id="349" class="Keyword">import</a> <a id="356" href="lists.flattening-lists.html" class="Module">lists.flattening-lists</a> <a id="379" class="Keyword">public</a>
<a id="386" class="Keyword">open</a> <a id="391" class="Keyword">import</a> <a id="398" href="lists.functoriality-finite-sequences.html" class="Module">lists.functoriality-finite-sequences</a> <a id="435" class="Keyword">public</a>
<a id="442" class="Keyword">open</a> <a id="447" class="Keyword">import</a> <a id="454" href="lists.functoriality-lists.html" class="Module">lists.functoriality-lists</a> <a id="480" class="Keyword">public</a>
<a id="487" class="Keyword">open</a> <a id="492" class="Keyword">import</a> <a id="499" href="lists.functoriality-tuples.html" class="Module">lists.functoriality-tuples</a> <a id="526" class="Keyword">public</a>
<a id="533" class="Keyword">open</a> <a id="538" class="Keyword">import</a> <a id="545" href="lists.functoriality-tuples-finite-sequences.html" class="Module">lists.functoriality-tuples-finite-sequences</a> <a id="589" class="Keyword">public</a>
<a id="596" class="Keyword">open</a> <a id="601" class="Keyword">import</a> <a id="608" href="lists.lists.html" class="Module">lists.lists</a> <a id="620" class="Keyword">public</a>
<a id="627" class="Keyword">open</a> <a id="632" class="Keyword">import</a> <a id="639" href="lists.lists-discrete-types.html" class="Module">lists.lists-discrete-types</a> <a id="666" class="Keyword">public</a>
<a id="673" class="Keyword">open</a> <a id="678" class="Keyword">import</a> <a id="685" href="lists.partial-sequences.html" class="Module">lists.partial-sequences</a> <a id="709" class="Keyword">public</a>
<a id="716" class="Keyword">open</a> <a id="721" class="Keyword">import</a> <a id="728" href="lists.permutation-lists.html" class="Module">lists.permutation-lists</a> <a id="752" class="Keyword">public</a>
<a id="759" class="Keyword">open</a> <a id="764" class="Keyword">import</a> <a id="771" href="lists.permutation-tuples.html" class="Module">lists.permutation-tuples</a> <a id="796" class="Keyword">public</a>
<a id="803" class="Keyword">open</a> <a id="808" class="Keyword">import</a> <a id="815" href="lists.predicates-on-lists.html" class="Module">lists.predicates-on-lists</a> <a id="841" class="Keyword">public</a>
<a id="848" class="Keyword">open</a> <a id="853" class="Keyword">import</a> <a id="860" href="lists.quicksort-lists.html" class="Module">lists.quicksort-lists</a> <a id="882" class="Keyword">public</a>
<a id="889" class="Keyword">open</a> <a id="894" class="Keyword">import</a> <a id="901" href="lists.repetitions-sequences.html" class="Module">lists.repetitions-sequences</a> <a id="929" class="Keyword">public</a>
<a id="936" class="Keyword">open</a> <a id="941" class="Keyword">import</a> <a id="948" href="lists.reversing-lists.html" class="Module">lists.reversing-lists</a> <a id="970" class="Keyword">public</a>
<a id="977" class="Keyword">open</a> <a id="982" class="Keyword">import</a> <a id="989" href="lists.sequences.html" class="Module">lists.sequences</a> <a id="1005" class="Keyword">public</a>
<a id="1012" class="Keyword">open</a> <a id="1017" class="Keyword">import</a> <a id="1024" href="lists.shifting-sequences.html" class="Module">lists.shifting-sequences</a> <a id="1049" class="Keyword">public</a>
<a id="1056" class="Keyword">open</a> <a id="1061" class="Keyword">import</a> <a id="1068" href="lists.sort-by-insertion-lists.html" class="Module">lists.sort-by-insertion-lists</a> <a id="1098" class="Keyword">public</a>
<a id="1105" class="Keyword">open</a> <a id="1110" class="Keyword">import</a> <a id="1117" href="lists.sort-by-insertion-tuples.html" class="Module">lists.sort-by-insertion-tuples</a> <a id="1148" class="Keyword">public</a>
<a id="1155" class="Keyword">open</a> <a id="1160" class="Keyword">import</a> <a id="1167" href="lists.sorted-lists.html" class="Module">lists.sorted-lists</a> <a id="1186" class="Keyword">public</a>
<a id="1193" class="Keyword">open</a> <a id="1198" class="Keyword">import</a> <a id="1205" href="lists.sorted-tuples.html" class="Module">lists.sorted-tuples</a> <a id="1225" class="Keyword">public</a>
<a id="1232" class="Keyword">open</a> <a id="1237" class="Keyword">import</a> <a id="1244" href="lists.sorting-algorithms-lists.html" class="Module">lists.sorting-algorithms-lists</a> <a id="1275" class="Keyword">public</a>
<a id="1282" class="Keyword">open</a> <a id="1287" class="Keyword">import</a> <a id="1294" href="lists.sorting-algorithms-tuples.html" class="Module">lists.sorting-algorithms-tuples</a> <a id="1326" class="Keyword">public</a>
<a id="1333" class="Keyword">open</a> <a id="1338" class="Keyword">import</a> <a id="1345" href="lists.subsequences.html" class="Module">lists.subsequences</a> <a id="1364" class="Keyword">public</a>
<a id="1371" class="Keyword">open</a> <a id="1376" class="Keyword">import</a> <a id="1383" href="lists.tuples.html" class="Module">lists.tuples</a> <a id="1396" class="Keyword">public</a>
<a id="1403" class="Keyword">open</a> <a id="1408" class="Keyword">import</a> <a id="1415" href="lists.universal-property-lists-wild-monoids.html" class="Module">lists.universal-property-lists-wild-monoids</a> <a id="1459" class="Keyword">public</a>
</pre>