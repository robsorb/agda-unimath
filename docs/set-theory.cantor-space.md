# Cantor space

<pre class="Agda"><a id="25" class="Keyword">module</a> <a id="32" href="set-theory.cantor-space.html" class="Module">set-theory.cantor-space</a> <a id="56" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="112" class="Keyword">open</a> <a id="117" class="Keyword">import</a> <a id="124" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="166" class="Keyword">open</a> <a id="171" class="Keyword">import</a> <a id="178" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="281" class="Keyword">open</a> <a id="286" class="Keyword">import</a> <a id="293" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="316" class="Keyword">open</a> <a id="321" class="Keyword">import</a> <a id="328" href="foundation.lawveres-fixed-point-theorem.html" class="Module">foundation.lawveres-fixed-point-theorem</a>
<a id="368" class="Keyword">open</a> <a id="373" class="Keyword">import</a> <a id="380" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="400" class="Keyword">open</a> <a id="405" class="Keyword">import</a> <a id="412" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="449" class="Keyword">open</a> <a id="454" class="Keyword">import</a> <a id="461" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="477" class="Keyword">open</a> <a id="482" class="Keyword">import</a> <a id="489" href="foundation.tight-apartness-relations.html" class="Module">foundation.tight-apartness-relations</a>
<a id="526" class="Keyword">open</a> <a id="531" class="Keyword">import</a> <a id="538" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="559" class="Keyword">open</a> <a id="564" class="Keyword">import</a> <a id="571" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="599" class="Keyword">open</a> <a id="604" class="Keyword">import</a> <a id="611" href="set-theory.cantors-diagonal-argument.html" class="Module">set-theory.cantors-diagonal-argument</a>
<a id="648" class="Keyword">open</a> <a id="653" class="Keyword">import</a> <a id="660" href="set-theory.countable-sets.html" class="Module">set-theory.countable-sets</a>
<a id="686" class="Keyword">open</a> <a id="691" class="Keyword">import</a> <a id="698" href="set-theory.uncountable-sets.html" class="Module">set-theory.uncountable-sets</a>

<a id="727" class="Keyword">open</a> <a id="732" class="Keyword">import</a> <a id="739" href="univalent-combinatorics.equality-standard-finite-types.html" class="Module">univalent-combinatorics.equality-standard-finite-types</a>
<a id="794" class="Keyword">open</a> <a id="799" class="Keyword">import</a> <a id="806" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

The
{{#concept "Cantor space" Disambiguation="as a type" Agda=cantor-space WD="Cantor space" WDID=Q616653}}
is the [set](foundation-core.sets.md) of
[functions](foundation-core.function-types.md) `ℕ → Fin 2`. In other words, it
is the set of [binary](foundation.booleans.md) [sequences](lists.sequences.md).

## Definition

<pre class="Agda"><a id="cantor-space"></a><a id="1210" href="set-theory.cantor-space.html#1210" class="Function">cantor-space</a> <a id="1223" class="Symbol">:</a> <a id="1225" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1228" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1234" href="set-theory.cantor-space.html#1210" class="Function">cantor-space</a> <a id="1247" class="Symbol">=</a> <a id="1249" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1251" class="Symbol">→</a> <a id="1253" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="1257" class="Number">2</a>
</pre>
## Properties

### The cantor space has a tight apartness relation

<pre class="Agda"><a id="cantor-space-Type-With-Tight-Apartness"></a><a id="1340" href="set-theory.cantor-space.html#1340" class="Function">cantor-space-Type-With-Tight-Apartness</a> <a id="1379" class="Symbol">:</a> <a id="1381" href="foundation.tight-apartness-relations.html#1830" class="Function">Type-With-Tight-Apartness</a> <a id="1407" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1413" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1419" href="set-theory.cantor-space.html#1340" class="Function">cantor-space-Type-With-Tight-Apartness</a> <a id="1458" class="Symbol">=</a>
  <a id="1462" href="foundation.tight-apartness-relations.html#3520" class="Function">exp-Type-With-Tight-Apartness</a> <a id="1492" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1494" class="Symbol">(</a><a id="1495" href="univalent-combinatorics.equality-standard-finite-types.html#5959" class="Function">Fin-Type-With-Tight-Apartness</a> <a id="1525" class="Number">2</a><a id="1526" class="Symbol">)</a>
</pre>
### The cantor space is a set

<pre class="Agda"><a id="is-set-cantor-space"></a><a id="1572" href="set-theory.cantor-space.html#1572" class="Function">is-set-cantor-space</a> <a id="1592" class="Symbol">:</a> <a id="1594" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="1601" href="set-theory.cantor-space.html#1210" class="Function">cantor-space</a>
<a id="1614" href="set-theory.cantor-space.html#1572" class="Function">is-set-cantor-space</a> <a id="1634" class="Symbol">=</a> <a id="1636" href="foundation.sets.html#3922" class="Function">is-set-function-type</a> <a id="1657" class="Symbol">(</a><a id="1658" href="univalent-combinatorics.standard-finite-types.html#2241" class="Function">is-set-Fin</a> <a id="1669" class="Number">2</a><a id="1670" class="Symbol">)</a>

<a id="cantor-space-Set"></a><a id="1673" href="set-theory.cantor-space.html#1673" class="Function">cantor-space-Set</a> <a id="1690" class="Symbol">:</a> <a id="1692" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="1696" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1702" href="set-theory.cantor-space.html#1673" class="Function">cantor-space-Set</a> <a id="1719" class="Symbol">=</a> <a id="1721" class="Symbol">(</a><a id="1722" href="set-theory.cantor-space.html#1210" class="Function">cantor-space</a> <a id="1735" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1737" href="set-theory.cantor-space.html#1572" class="Function">is-set-cantor-space</a><a id="1756" class="Symbol">)</a>
</pre>
### The cantor space is uncountable

<pre class="Agda"><a id="is-uncountable-cantor-space"></a><a id="1808" href="set-theory.cantor-space.html#1808" class="Function">is-uncountable-cantor-space</a> <a id="1836" class="Symbol">:</a> <a id="1838" href="set-theory.uncountable-sets.html#821" class="Function">is-uncountable</a> <a id="1853" href="set-theory.cantor-space.html#1673" class="Function">cantor-space-Set</a>
<a id="1870" href="set-theory.cantor-space.html#1808" class="Function">is-uncountable-cantor-space</a> <a id="1898" class="Symbol">=</a>
  <a id="1902" href="set-theory.cantors-diagonal-argument.html#6015" class="Function">is-uncountable-sequence-discrete-type-diagonal-argument-Cantor</a>
    <a id="1969" class="Symbol">(</a> <a id="1971" href="univalent-combinatorics.equality-standard-finite-types.html#3247" class="Function">Fin-Discrete-Type</a> <a id="1989" class="Number">2</a><a id="1990" class="Symbol">)</a>
    <a id="1996" class="Symbol">(</a> <a id="1998" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="2002" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a><a id="2006" class="Symbol">)</a>
    <a id="2012" class="Symbol">(</a> <a id="2014" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="2018" class="Symbol">(</a><a id="2019" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="2023" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a><a id="2027" class="Symbol">))</a>
    <a id="2034" class="Symbol">(</a> <a id="2036" href="foundation.coproduct-types.html#2987" class="Function">neq-inr-inl</a><a id="2047" class="Symbol">)</a>
</pre>
## External links

- [Cantor space](https://en.wikipedia.org/wiki/Cantor_space) at Wikipedia
- [Cantor space](https://ncatlab.org/nlab/show/Cantor+space) at $n$Lab
