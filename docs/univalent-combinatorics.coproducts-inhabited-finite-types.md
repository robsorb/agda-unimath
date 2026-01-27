# Coproducts of inhabited finite types

<pre class="Agda"><a id="49" class="Keyword">module</a> <a id="56" href="univalent-combinatorics.coproducts-inhabited-finite-types.html" class="Module">univalent-combinatorics.coproducts-inhabited-finite-types</a> <a id="114" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="170" class="Keyword">open</a> <a id="175" class="Keyword">import</a> <a id="182" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="209" class="Keyword">open</a> <a id="214" class="Keyword">import</a> <a id="221" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="253" class="Keyword">open</a> <a id="258" class="Keyword">import</a> <a id="265" href="foundation.inhabited-types.html" class="Module">foundation.inhabited-types</a>
<a id="292" class="Keyword">open</a> <a id="297" class="Keyword">import</a> <a id="304" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="univalent-combinatorics.coproduct-types.html" class="Module">univalent-combinatorics.coproduct-types</a>
<a id="384" class="Keyword">open</a> <a id="389" class="Keyword">import</a> <a id="396" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="433" class="Keyword">open</a> <a id="438" class="Keyword">import</a> <a id="445" href="univalent-combinatorics.inhabited-finite-types.html" class="Module">univalent-combinatorics.inhabited-finite-types</a>
</pre>
</details>

## Idea

The [coproduct](univalent-combinatorics.coproduct-types.md) of two
[inhabited finite types](univalent-combinatorics.inhabited-finite-types.md) is
itself an inhabited finite type.

## Definition

<pre class="Agda"><a id="coproduct-Inhabited-Finite-Type"></a><a id="721" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#721" class="Function">coproduct-Inhabited-Finite-Type</a> <a id="753" class="Symbol">:</a>
  <a id="757" class="Symbol">{</a><a id="758" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#758" class="Bound">l1</a> <a id="761" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#761" class="Bound">l2</a> <a id="764" class="Symbol">:</a> <a id="766" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="771" class="Symbol">}</a> <a id="773" class="Symbol">→</a> <a id="775" href="univalent-combinatorics.inhabited-finite-types.html#1273" class="Function">Inhabited-Finite-Type</a> <a id="797" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#758" class="Bound">l1</a> <a id="800" class="Symbol">→</a> <a id="802" href="univalent-combinatorics.inhabited-finite-types.html#1273" class="Function">Inhabited-Finite-Type</a> <a id="824" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#761" class="Bound">l2</a> <a id="827" class="Symbol">→</a>
  <a id="831" href="univalent-combinatorics.inhabited-finite-types.html#1273" class="Function">Inhabited-Finite-Type</a> <a id="853" class="Symbol">(</a><a id="854" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#758" class="Bound">l1</a> <a id="857" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="859" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#761" class="Bound">l2</a><a id="861" class="Symbol">)</a>
<a id="863" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="867" class="Symbol">(</a><a id="868" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#721" class="Function">coproduct-Inhabited-Finite-Type</a> <a id="900" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#900" class="Bound">X</a> <a id="902" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#902" class="Bound">Y</a><a id="903" class="Symbol">)</a> <a id="905" class="Symbol">=</a>
  <a id="909" href="univalent-combinatorics.coproduct-types.html#9191" class="Function">coproduct-Finite-Type</a>
    <a id="935" class="Symbol">(</a> <a id="937" href="univalent-combinatorics.inhabited-finite-types.html#1476" class="Function">finite-type-Inhabited-Finite-Type</a> <a id="971" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#900" class="Bound">X</a><a id="972" class="Symbol">)</a>
    <a id="978" class="Symbol">(</a> <a id="980" href="univalent-combinatorics.inhabited-finite-types.html#1476" class="Function">finite-type-Inhabited-Finite-Type</a> <a id="1014" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#902" class="Bound">Y</a><a id="1015" class="Symbol">)</a>
<a id="1017" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1021" class="Symbol">(</a><a id="1022" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#721" class="Function">coproduct-Inhabited-Finite-Type</a> <a id="1054" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#1054" class="Bound">X</a> <a id="1056" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#1056" class="Bound">Y</a><a id="1057" class="Symbol">)</a> <a id="1059" class="Symbol">=</a>
  <a id="1063" href="foundation.inhabited-types.html#6262" class="Function">map-is-inhabited</a> <a id="1080" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="1084" class="Symbol">(</a><a id="1085" href="univalent-combinatorics.inhabited-finite-types.html#1871" class="Function">is-inhabited-type-Inhabited-Finite-Type</a> <a id="1125" href="univalent-combinatorics.coproducts-inhabited-finite-types.html#1054" class="Bound">X</a><a id="1126" class="Symbol">)</a>
</pre>