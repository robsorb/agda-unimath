# Bracelets

<pre class="Agda"><a id="22" class="Keyword">module</a> <a id="29" href="univalent-combinatorics.bracelets.html" class="Module">univalent-combinatorics.bracelets</a> <a id="63" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="119" class="Keyword">open</a> <a id="124" class="Keyword">import</a> <a id="131" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="173" class="Keyword">open</a> <a id="178" class="Keyword">import</a> <a id="185" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="217" class="Keyword">open</a> <a id="222" class="Keyword">import</a> <a id="229" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="graph-theory.polygons.html" class="Module">graph-theory.polygons</a>

<a id="292" class="Keyword">open</a> <a id="297" class="Keyword">import</a> <a id="304" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Definition

### Bracelets

<pre class="Agda"><a id="bracelet"></a><a id="405" href="univalent-combinatorics.bracelets.html#405" class="Function">bracelet</a> <a id="414" class="Symbol">:</a> <a id="416" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="418" class="Symbol">→</a> <a id="420" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="422" class="Symbol">→</a> <a id="424" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="427" class="Symbol">(</a><a id="428" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="433" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="438" class="Symbol">)</a>
<a id="440" href="univalent-combinatorics.bracelets.html#405" class="Function">bracelet</a> <a id="449" href="univalent-combinatorics.bracelets.html#449" class="Bound">m</a> <a id="451" href="univalent-combinatorics.bracelets.html#451" class="Bound">n</a> <a id="453" class="Symbol">=</a> <a id="455" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="457" class="Symbol">(</a><a id="458" href="graph-theory.polygons.html#2279" class="Function">Polygon</a> <a id="466" href="univalent-combinatorics.bracelets.html#449" class="Bound">m</a><a id="467" class="Symbol">)</a> <a id="469" class="Symbol">(λ</a> <a id="472" href="univalent-combinatorics.bracelets.html#472" class="Bound">X</a> <a id="474" class="Symbol">→</a> <a id="476" href="graph-theory.polygons.html#2735" class="Function">vertex-Polygon</a> <a id="491" href="univalent-combinatorics.bracelets.html#449" class="Bound">m</a> <a id="493" href="univalent-combinatorics.bracelets.html#472" class="Bound">X</a> <a id="495" class="Symbol">→</a> <a id="497" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="501" href="univalent-combinatorics.bracelets.html#451" class="Bound">n</a><a id="502" class="Symbol">)</a>
</pre>
## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
