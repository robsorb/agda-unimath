# Finitely enumerable subsets of the real numbers

<pre class="Agda"><a id="60" class="Keyword">module</a> <a id="67" href="real-numbers.finitely-enumerable-subsets-real-numbers.html" class="Module">real-numbers.finitely-enumerable-subsets-real-numbers</a> <a id="121" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="foundation.involutions.html" class="Module">foundation.involutions</a>
<a id="256" class="Keyword">open</a> <a id="261" class="Keyword">import</a> <a id="268" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="288" class="Keyword">open</a> <a id="293" class="Keyword">import</a> <a id="300" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="real-numbers.dedekind-real-numbers.html" class="Module">real-numbers.dedekind-real-numbers</a>
<a id="375" class="Keyword">open</a> <a id="380" class="Keyword">import</a> <a id="387" href="real-numbers.negation-real-numbers.html" class="Module">real-numbers.negation-real-numbers</a>
<a id="422" class="Keyword">open</a> <a id="427" class="Keyword">import</a> <a id="434" href="real-numbers.subsets-real-numbers.html" class="Module">real-numbers.subsets-real-numbers</a>

<a id="469" class="Keyword">open</a> <a id="474" class="Keyword">import</a> <a id="481" href="univalent-combinatorics.finitely-enumerable-subtypes.html" class="Module">univalent-combinatorics.finitely-enumerable-subtypes</a>
<a id="534" class="Keyword">open</a> <a id="539" class="Keyword">import</a> <a id="546" href="univalent-combinatorics.finitely-enumerable-types.html" class="Module">univalent-combinatorics.finitely-enumerable-types</a>
</pre>
</details>

## Idea

A [subset of the real numbers](real-numbers.subsets-real-numbers.md) is
{{#concept "finitely enumerable" disambiguation="subset of the real numbers" Agda=finitely-enumerable-subset-ℝ}}
if it is
[finitely enumerable](univalent-combinatorics.finitely-enumerable-subtypes.md)
as a [subtype](foundation.subtypes.md) of the
[real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

<pre class="Agda"><a id="finitely-enumerable-subset-ℝ"></a><a id="1020" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1020" class="Function">finitely-enumerable-subset-ℝ</a> <a id="1049" class="Symbol">:</a> <a id="1051" class="Symbol">(</a><a id="1052" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1052" class="Bound">l1</a> <a id="1055" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1055" class="Bound">l2</a> <a id="1058" class="Symbol">:</a> <a id="1060" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1065" class="Symbol">)</a> <a id="1067" class="Symbol">→</a> <a id="1069" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1072" class="Symbol">(</a><a id="1073" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1078" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1052" class="Bound">l1</a> <a id="1081" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1083" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1088" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1055" class="Bound">l2</a><a id="1090" class="Symbol">)</a>
<a id="1092" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1020" class="Function">finitely-enumerable-subset-ℝ</a> <a id="1121" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1121" class="Bound">l1</a> <a id="1124" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1124" class="Bound">l2</a> <a id="1127" class="Symbol">=</a> <a id="1129" href="univalent-combinatorics.finitely-enumerable-subtypes.html#1671" class="Function">finitely-enumerable-subtype</a> <a id="1157" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1121" class="Bound">l1</a> <a id="1160" class="Symbol">(</a><a id="1161" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="1163" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1124" class="Bound">l2</a><a id="1165" class="Symbol">)</a>

<a id="1168" class="Keyword">module</a> <a id="1175" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1175" class="Module">_</a>
  <a id="1179" class="Symbol">{</a><a id="1180" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1180" class="Bound">l1</a> <a id="1183" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1183" class="Bound">l2</a> <a id="1186" class="Symbol">:</a> <a id="1188" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1193" class="Symbol">}</a> <a id="1195" class="Symbol">(</a><a id="1196" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1196" class="Bound">S</a> <a id="1198" class="Symbol">:</a> <a id="1200" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1020" class="Function">finitely-enumerable-subset-ℝ</a> <a id="1229" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1180" class="Bound">l1</a> <a id="1232" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1183" class="Bound">l2</a><a id="1234" class="Symbol">)</a>
  <a id="1238" class="Keyword">where</a>

  <a id="1247" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1247" class="Function">subset-finitely-enumerable-subset-ℝ</a> <a id="1283" class="Symbol">:</a> <a id="1285" href="real-numbers.subsets-real-numbers.html#1495" class="Function">subset-ℝ</a> <a id="1294" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1180" class="Bound">l1</a> <a id="1297" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1183" class="Bound">l2</a>
  <a id="1302" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1247" class="Function">subset-finitely-enumerable-subset-ℝ</a> <a id="1338" class="Symbol">=</a> <a id="1340" href="univalent-combinatorics.finitely-enumerable-subtypes.html#1957" class="Function">subtype-finitely-enumerable-subtype</a> <a id="1376" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1196" class="Bound">S</a>

  <a id="1381" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1381" class="Function">type-finitely-enumerable-subset-ℝ</a> <a id="1415" class="Symbol">:</a> <a id="1417" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1420" class="Symbol">(</a><a id="1421" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1180" class="Bound">l1</a> <a id="1424" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1426" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1431" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1183" class="Bound">l2</a><a id="1433" class="Symbol">)</a>
  <a id="1437" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1381" class="Function">type-finitely-enumerable-subset-ℝ</a> <a id="1471" class="Symbol">=</a>
    <a id="1477" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="1490" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1247" class="Function">subset-finitely-enumerable-subset-ℝ</a>

  <a id="1529" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1529" class="Function">is-finitely-enumerable-finitely-enumerable-subset-ℝ</a> <a id="1581" class="Symbol">:</a>
    <a id="1587" href="univalent-combinatorics.finitely-enumerable-subtypes.html#1549" class="Function">is-finitely-enumerable-subtype</a> <a id="1618" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1247" class="Function">subset-finitely-enumerable-subset-ℝ</a>
  <a id="1656" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1529" class="Function">is-finitely-enumerable-finitely-enumerable-subset-ℝ</a> <a id="1708" class="Symbol">=</a>
    <a id="1714" href="univalent-combinatorics.finitely-enumerable-subtypes.html#2057" class="Function">is-finitely-enumerable-subtype-finitely-enumerable-subtype</a> <a id="1773" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1196" class="Bound">S</a>

  <a id="1778" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1778" class="Function">inclusion-finitely-enumerable-subset-ℝ</a> <a id="1817" class="Symbol">:</a>
    <a id="1823" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1381" class="Function">type-finitely-enumerable-subset-ℝ</a> <a id="1857" class="Symbol">→</a> <a id="1859" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="1861" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1183" class="Bound">l2</a>
  <a id="1866" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1778" class="Function">inclusion-finitely-enumerable-subset-ℝ</a> <a id="1905" class="Symbol">=</a>
    <a id="1911" href="foundation-core.subtypes.html#1842" class="Function">inclusion-subtype</a> <a id="1929" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1247" class="Function">subset-finitely-enumerable-subset-ℝ</a>
</pre>
## Properties

### The elementwise negation of a finitely enumerable subset of real numbers

<pre class="Agda"><a id="neg-finitely-enumerable-subset-ℝ"></a><a id="2071" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#2071" class="Function">neg-finitely-enumerable-subset-ℝ</a> <a id="2104" class="Symbol">:</a>
  <a id="2108" class="Symbol">{</a><a id="2109" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#2109" class="Bound">l1</a> <a id="2112" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#2112" class="Bound">l2</a> <a id="2115" class="Symbol">:</a> <a id="2117" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2122" class="Symbol">}</a> <a id="2124" class="Symbol">→</a>
  <a id="2128" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1020" class="Function">finitely-enumerable-subset-ℝ</a> <a id="2157" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#2109" class="Bound">l1</a> <a id="2160" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#2112" class="Bound">l2</a> <a id="2163" class="Symbol">→</a> <a id="2165" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1020" class="Function">finitely-enumerable-subset-ℝ</a> <a id="2194" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#2109" class="Bound">l1</a> <a id="2197" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#2112" class="Bound">l2</a>
<a id="2200" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#2071" class="Function">neg-finitely-enumerable-subset-ℝ</a> <a id="2233" class="Symbol">(</a><a id="2234" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#2234" class="Bound">S</a> <a id="2236" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2238" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#2238" class="Bound">is-finitely-enumerable-S</a><a id="2262" class="Symbol">)</a> <a id="2264" class="Symbol">=</a>
  <a id="2268" class="Symbol">(</a> <a id="2270" href="real-numbers.subsets-real-numbers.html#2491" class="Function">neg-subset-ℝ</a> <a id="2283" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#2234" class="Bound">S</a> <a id="2285" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="2291" href="univalent-combinatorics.finitely-enumerable-types.html#3987" class="Function">is-finitely-enumerable-equiv</a>
      <a id="2326" class="Symbol">(</a> <a id="2328" href="foundation.subtypes.html#4178" class="Function">equiv-precomp-equiv-type-subtype</a> <a id="2361" class="Symbol">(</a><a id="2362" href="foundation.involutions.html#2083" class="Function">equiv-is-involution</a> <a id="2382" href="real-numbers.negation-real-numbers.html#3138" class="Function">neg-neg-ℝ</a><a id="2391" class="Symbol">)</a> <a id="2393" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#2234" class="Bound">S</a><a id="2394" class="Symbol">)</a>
      <a id="2402" class="Symbol">(</a> <a id="2404" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#2238" class="Bound">is-finitely-enumerable-S</a><a id="2428" class="Symbol">))</a>
</pre>