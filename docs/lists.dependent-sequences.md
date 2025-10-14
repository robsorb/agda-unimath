# Dependent sequences

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="lists.dependent-sequences.html" class="Module">lists.dependent-sequences</a> <a id="65" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="121" class="Keyword">open</a> <a id="126" class="Keyword">import</a> <a id="133" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="175" class="Keyword">open</a> <a id="180" class="Keyword">import</a> <a id="187" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
</pre>
</details>

## Idea

A **dependent sequence** of elements in a family of types `A : ℕ → UU` is a
dependent map `(n : ℕ) → A n`.

## Definition

### Dependent sequences of elements in a family of types

<pre class="Agda"><a id="dependent-sequence"></a><a id="473" href="lists.dependent-sequences.html#473" class="Function">dependent-sequence</a> <a id="492" class="Symbol">:</a> <a id="494" class="Symbol">{</a><a id="495" href="lists.dependent-sequences.html#495" class="Bound">l</a> <a id="497" class="Symbol">:</a> <a id="499" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="504" class="Symbol">}</a> <a id="506" class="Symbol">→</a> <a id="508" class="Symbol">(</a><a id="509" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="511" class="Symbol">→</a> <a id="513" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="516" href="lists.dependent-sequences.html#495" class="Bound">l</a><a id="517" class="Symbol">)</a> <a id="519" class="Symbol">→</a> <a id="521" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="524" href="lists.dependent-sequences.html#495" class="Bound">l</a>
<a id="526" href="lists.dependent-sequences.html#473" class="Function">dependent-sequence</a> <a id="545" href="lists.dependent-sequences.html#545" class="Bound">B</a> <a id="547" class="Symbol">=</a> <a id="549" class="Symbol">(</a><a id="550" href="lists.dependent-sequences.html#550" class="Bound">n</a> <a id="552" class="Symbol">:</a> <a id="554" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="555" class="Symbol">)</a> <a id="557" class="Symbol">→</a> <a id="559" href="lists.dependent-sequences.html#545" class="Bound">B</a> <a id="561" href="lists.dependent-sequences.html#550" class="Bound">n</a>
</pre>
### Functorial action on maps of dependent sequences

<pre class="Agda"><a id="map-dependent-sequence"></a><a id="630" href="lists.dependent-sequences.html#630" class="Function">map-dependent-sequence</a> <a id="653" class="Symbol">:</a>
  <a id="657" class="Symbol">{</a><a id="658" href="lists.dependent-sequences.html#658" class="Bound">l1</a> <a id="661" href="lists.dependent-sequences.html#661" class="Bound">l2</a> <a id="664" class="Symbol">:</a> <a id="666" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="671" class="Symbol">}</a> <a id="673" class="Symbol">{</a><a id="674" href="lists.dependent-sequences.html#674" class="Bound">A</a> <a id="676" class="Symbol">:</a> <a id="678" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="680" class="Symbol">→</a> <a id="682" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="685" href="lists.dependent-sequences.html#658" class="Bound">l1</a><a id="687" class="Symbol">}</a> <a id="689" class="Symbol">{</a><a id="690" href="lists.dependent-sequences.html#690" class="Bound">B</a> <a id="692" class="Symbol">:</a> <a id="694" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="696" class="Symbol">→</a> <a id="698" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="701" href="lists.dependent-sequences.html#661" class="Bound">l2</a><a id="703" class="Symbol">}</a> <a id="705" class="Symbol">→</a>
  <a id="709" class="Symbol">((</a><a id="711" href="lists.dependent-sequences.html#711" class="Bound">n</a> <a id="713" class="Symbol">:</a> <a id="715" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="716" class="Symbol">)</a> <a id="718" class="Symbol">→</a> <a id="720" href="lists.dependent-sequences.html#674" class="Bound">A</a> <a id="722" href="lists.dependent-sequences.html#711" class="Bound">n</a> <a id="724" class="Symbol">→</a> <a id="726" href="lists.dependent-sequences.html#690" class="Bound">B</a> <a id="728" href="lists.dependent-sequences.html#711" class="Bound">n</a><a id="729" class="Symbol">)</a> <a id="731" class="Symbol">→</a> <a id="733" href="lists.dependent-sequences.html#473" class="Function">dependent-sequence</a> <a id="752" href="lists.dependent-sequences.html#674" class="Bound">A</a> <a id="754" class="Symbol">→</a> <a id="756" href="lists.dependent-sequences.html#473" class="Function">dependent-sequence</a> <a id="775" href="lists.dependent-sequences.html#690" class="Bound">B</a>
<a id="777" href="lists.dependent-sequences.html#630" class="Function">map-dependent-sequence</a> <a id="800" href="lists.dependent-sequences.html#800" class="Bound">f</a> <a id="802" href="lists.dependent-sequences.html#802" class="Bound">a</a> <a id="804" class="Symbol">=</a> <a id="806" href="foundation-core.function-types.html#974" class="Function">map-Π</a> <a id="812" href="lists.dependent-sequences.html#800" class="Bound">f</a> <a id="814" href="lists.dependent-sequences.html#802" class="Bound">a</a>
</pre>