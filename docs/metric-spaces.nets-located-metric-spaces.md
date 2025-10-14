# Nets in located metric spaces

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="metric-spaces.nets-located-metric-spaces.html" class="Module">metric-spaces.nets-located-metric-spaces</a> <a id="90" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="146" class="Keyword">open</a> <a id="151" class="Keyword">import</a> <a id="158" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="elementary-number-theory.positive-rational-numbers.html" class="Module">elementary-number-theory.positive-rational-numbers</a>

<a id="263" class="Keyword">open</a> <a id="268" class="Keyword">import</a> <a id="275" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="307" class="Keyword">open</a> <a id="312" class="Keyword">import</a> <a id="319" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="342" class="Keyword">open</a> <a id="347" class="Keyword">import</a> <a id="354" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="392" class="Keyword">open</a> <a id="397" class="Keyword">import</a> <a id="404" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="441" class="Keyword">open</a> <a id="446" class="Keyword">import</a> <a id="453" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="477" class="Keyword">open</a> <a id="482" class="Keyword">import</a> <a id="489" href="foundation.raising-universe-levels.html" class="Module">foundation.raising-universe-levels</a>
<a id="524" class="Keyword">open</a> <a id="529" class="Keyword">import</a> <a id="536" href="foundation.singleton-subtypes.html" class="Module">foundation.singleton-subtypes</a>
<a id="566" class="Keyword">open</a> <a id="571" class="Keyword">import</a> <a id="578" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="598" class="Keyword">open</a> <a id="603" class="Keyword">import</a> <a id="610" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="637" class="Keyword">open</a> <a id="642" class="Keyword">import</a> <a id="649" href="foundation.torsorial-type-families.html" class="Module">foundation.torsorial-type-families</a>
<a id="684" class="Keyword">open</a> <a id="689" class="Keyword">import</a> <a id="696" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="724" class="Keyword">open</a> <a id="729" class="Keyword">import</a> <a id="736" href="metric-spaces.approximations-metric-spaces.html" class="Module">metric-spaces.approximations-metric-spaces</a>
<a id="779" class="Keyword">open</a> <a id="784" class="Keyword">import</a> <a id="791" href="metric-spaces.located-metric-spaces.html" class="Module">metric-spaces.located-metric-spaces</a>
<a id="827" class="Keyword">open</a> <a id="832" class="Keyword">import</a> <a id="839" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
<a id="867" class="Keyword">open</a> <a id="872" class="Keyword">import</a> <a id="879" href="metric-spaces.nets-metric-spaces.html" class="Module">metric-spaces.nets-metric-spaces</a>

<a id="913" class="Keyword">open</a> <a id="918" class="Keyword">import</a> <a id="925" href="univalent-combinatorics.finite-subtypes.html" class="Module">univalent-combinatorics.finite-subtypes</a>
<a id="965" class="Keyword">open</a> <a id="970" class="Keyword">import</a> <a id="977" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="1014" class="Keyword">open</a> <a id="1019" class="Keyword">import</a> <a id="1026" href="univalent-combinatorics.finitely-enumerable-subtypes.html" class="Module">univalent-combinatorics.finitely-enumerable-subtypes</a>
<a id="1079" class="Keyword">open</a> <a id="1084" class="Keyword">import</a> <a id="1091" href="univalent-combinatorics.finitely-enumerable-types.html" class="Module">univalent-combinatorics.finitely-enumerable-types</a>
<a id="1141" class="Keyword">open</a> <a id="1146" class="Keyword">import</a> <a id="1153" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

For an `ε : ℚ⁺`, an
`ε`-{{#concept "net" disambiguation="in a located metric space" Agda=net-Located-Metric-Space}}
to a [located metric space](metric-spaces.located-metric-spaces.md) `X` is an
[`ε`-net](metric-spaces.nets-metric-spaces.md) in the underlying
[metric space](metric-spaces.metric-spaces.md).

## Definition

<pre class="Agda"><a id="net-Located-Metric-Space"></a><a id="1556" href="metric-spaces.nets-located-metric-spaces.html#1556" class="Function">net-Located-Metric-Space</a> <a id="1581" class="Symbol">:</a>
  <a id="1585" class="Symbol">{</a><a id="1586" href="metric-spaces.nets-located-metric-spaces.html#1586" class="Bound">l1</a> <a id="1589" href="metric-spaces.nets-located-metric-spaces.html#1589" class="Bound">l2</a> <a id="1592" class="Symbol">:</a> <a id="1594" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1599" class="Symbol">}</a> <a id="1601" class="Symbol">(</a><a id="1602" href="metric-spaces.nets-located-metric-spaces.html#1602" class="Bound">l3</a> <a id="1605" class="Symbol">:</a> <a id="1607" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1612" class="Symbol">)</a> <a id="1614" class="Symbol">→</a> <a id="1616" href="metric-spaces.located-metric-spaces.html#2868" class="Function">Located-Metric-Space</a> <a id="1637" href="metric-spaces.nets-located-metric-spaces.html#1586" class="Bound">l1</a> <a id="1640" href="metric-spaces.nets-located-metric-spaces.html#1589" class="Bound">l2</a> <a id="1643" class="Symbol">→</a> <a id="1645" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a> <a id="1648" class="Symbol">→</a>
  <a id="1652" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1655" class="Symbol">(</a><a id="1656" href="metric-spaces.nets-located-metric-spaces.html#1586" class="Bound">l1</a> <a id="1659" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1661" href="metric-spaces.nets-located-metric-spaces.html#1589" class="Bound">l2</a> <a id="1664" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1666" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1671" href="metric-spaces.nets-located-metric-spaces.html#1602" class="Bound">l3</a><a id="1673" class="Symbol">)</a>
<a id="1675" href="metric-spaces.nets-located-metric-spaces.html#1556" class="Function">net-Located-Metric-Space</a> <a id="1700" href="metric-spaces.nets-located-metric-spaces.html#1700" class="Bound">l3</a> <a id="1703" href="metric-spaces.nets-located-metric-spaces.html#1703" class="Bound">X</a> <a id="1705" class="Symbol">=</a>
  <a id="1709" href="metric-spaces.nets-metric-spaces.html#2016" class="Function">net-Metric-Space</a> <a id="1726" href="metric-spaces.nets-located-metric-spaces.html#1700" class="Bound">l3</a> <a id="1729" class="Symbol">(</a><a id="1730" href="metric-spaces.located-metric-spaces.html#3089" class="Function">metric-space-Located-Metric-Space</a> <a id="1764" href="metric-spaces.nets-located-metric-spaces.html#1703" class="Bound">X</a><a id="1765" class="Symbol">)</a>
</pre>