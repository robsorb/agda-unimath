# The maybe monad on finite types

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="univalent-combinatorics.maybe.html" class="Module">univalent-combinatorics.maybe</a> <a id="81" class="Keyword">where</a>

<a id="88" class="Keyword">open</a> <a id="93" class="Keyword">import</a> <a id="100" href="foundation.maybe.html" class="Module">foundation.maybe</a> <a id="117" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="174" class="Keyword">open</a> <a id="179" class="Keyword">import</a> <a id="186" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="228" class="Keyword">open</a> <a id="233" class="Keyword">import</a> <a id="240" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="268" class="Keyword">open</a> <a id="273" class="Keyword">import</a> <a id="280" href="univalent-combinatorics.coproduct-types.html" class="Module">univalent-combinatorics.coproduct-types</a>
<a id="320" class="Keyword">open</a> <a id="325" class="Keyword">import</a> <a id="332" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

<pre class="Agda"><a id="add-free-point-Type-With-Cardinality-ℕ"></a><a id="394" href="univalent-combinatorics.maybe.html#394" class="Function">add-free-point-Type-With-Cardinality-ℕ</a> <a id="433" class="Symbol">:</a>
  <a id="437" class="Symbol">{</a><a id="438" href="univalent-combinatorics.maybe.html#438" class="Bound">l1</a> <a id="441" class="Symbol">:</a> <a id="443" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="448" class="Symbol">}</a> <a id="450" class="Symbol">(</a><a id="451" href="univalent-combinatorics.maybe.html#451" class="Bound">k</a> <a id="453" class="Symbol">:</a> <a id="455" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="456" class="Symbol">)</a> <a id="458" class="Symbol">→</a>
  <a id="462" href="univalent-combinatorics.finite-types.html#3324" class="Function">Type-With-Cardinality-ℕ</a> <a id="486" href="univalent-combinatorics.maybe.html#438" class="Bound">l1</a> <a id="489" href="univalent-combinatorics.maybe.html#451" class="Bound">k</a> <a id="491" class="Symbol">→</a>
  <a id="495" href="univalent-combinatorics.finite-types.html#3324" class="Function">Type-With-Cardinality-ℕ</a> <a id="519" href="univalent-combinatorics.maybe.html#438" class="Bound">l1</a> <a id="522" class="Symbol">(</a><a id="523" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="530" href="univalent-combinatorics.maybe.html#451" class="Bound">k</a><a id="531" class="Symbol">)</a>
<a id="533" href="univalent-combinatorics.maybe.html#394" class="Function">add-free-point-Type-With-Cardinality-ℕ</a> <a id="572" href="univalent-combinatorics.maybe.html#572" class="Bound">k</a> <a id="574" href="univalent-combinatorics.maybe.html#574" class="Bound">X</a> <a id="576" class="Symbol">=</a>
  <a id="580" href="univalent-combinatorics.coproduct-types.html#9869" class="Function">coproduct-Type-With-Cardinality-ℕ</a> <a id="614" href="univalent-combinatorics.maybe.html#572" class="Bound">k</a> <a id="616" class="Number">1</a> <a id="618" href="univalent-combinatorics.maybe.html#574" class="Bound">X</a> <a id="620" href="univalent-combinatorics.finite-types.html#6977" class="Function">unit-Type-With-Cardinality-ℕ</a>
</pre>