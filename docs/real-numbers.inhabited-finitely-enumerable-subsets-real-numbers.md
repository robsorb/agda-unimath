# Inhabited finitely enumerable subsets of the real numbers

<pre class="Agda"><a id="70" class="Keyword">module</a> <a id="77" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html" class="Module">real-numbers.inhabited-finitely-enumerable-subsets-real-numbers</a> <a id="141" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="241" class="Keyword">open</a> <a id="246" class="Keyword">import</a> <a id="253" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="277" class="Keyword">open</a> <a id="282" class="Keyword">import</a> <a id="289" href="foundation.inhabited-types.html" class="Module">foundation.inhabited-types</a>
<a id="316" class="Keyword">open</a> <a id="321" class="Keyword">import</a> <a id="328" href="foundation.involutions.html" class="Module">foundation.involutions</a>
<a id="351" class="Keyword">open</a> <a id="356" class="Keyword">import</a> <a id="363" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="383" class="Keyword">open</a> <a id="388" class="Keyword">import</a> <a id="395" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="423" class="Keyword">open</a> <a id="428" class="Keyword">import</a> <a id="435" href="real-numbers.dedekind-real-numbers.html" class="Module">real-numbers.dedekind-real-numbers</a>
<a id="470" class="Keyword">open</a> <a id="475" class="Keyword">import</a> <a id="482" href="real-numbers.finitely-enumerable-subsets-real-numbers.html" class="Module">real-numbers.finitely-enumerable-subsets-real-numbers</a>
<a id="536" class="Keyword">open</a> <a id="541" class="Keyword">import</a> <a id="548" href="real-numbers.negation-real-numbers.html" class="Module">real-numbers.negation-real-numbers</a>
<a id="583" class="Keyword">open</a> <a id="588" class="Keyword">import</a> <a id="595" href="real-numbers.subsets-real-numbers.html" class="Module">real-numbers.subsets-real-numbers</a>

<a id="630" class="Keyword">open</a> <a id="635" class="Keyword">import</a> <a id="642" href="univalent-combinatorics.finitely-enumerable-subtypes.html" class="Module">univalent-combinatorics.finitely-enumerable-subtypes</a>
<a id="695" class="Keyword">open</a> <a id="700" class="Keyword">import</a> <a id="707" href="univalent-combinatorics.finitely-enumerable-types.html" class="Module">univalent-combinatorics.finitely-enumerable-types</a>
<a id="757" class="Keyword">open</a> <a id="762" class="Keyword">import</a> <a id="769" href="univalent-combinatorics.inhabited-finitely-enumerable-subtypes.html" class="Module">univalent-combinatorics.inhabited-finitely-enumerable-subtypes</a>
</pre>
</details>

## Idea

An
{{#concept "inhabited finitely enumerable subset" Agda=inhabited-finitely-enumerable-subset-ℝ}}
of the [real numbers](real-numbers.dedekind-real-numbers.md) is a
[subtype](foundation.subtypes.md) of `ℝ` that is
[inhabited and finitely enumerable](univalent-combinatorics.inhabited-finitely-enumerable-subtypes.md).

## Definition

<pre class="Agda"><a id="inhabited-finitely-enumerable-subset-ℝ"></a><a id="1200" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1200" class="Function">inhabited-finitely-enumerable-subset-ℝ</a> <a id="1239" class="Symbol">:</a>
  <a id="1243" class="Symbol">(</a><a id="1244" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1244" class="Bound">l1</a> <a id="1247" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1247" class="Bound">l2</a> <a id="1250" class="Symbol">:</a> <a id="1252" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1257" class="Symbol">)</a> <a id="1259" class="Symbol">→</a> <a id="1261" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1264" class="Symbol">(</a><a id="1265" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1270" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1244" class="Bound">l1</a> <a id="1273" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1275" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1280" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1247" class="Bound">l2</a><a id="1282" class="Symbol">)</a>
<a id="1284" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1200" class="Function">inhabited-finitely-enumerable-subset-ℝ</a> <a id="1323" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1323" class="Bound">l1</a> <a id="1326" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1326" class="Bound">l2</a> <a id="1329" class="Symbol">=</a>
  <a id="1333" href="univalent-combinatorics.inhabited-finitely-enumerable-subtypes.html#1118" class="Function">inhabited-finitely-enumerable-subtype</a> <a id="1371" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1323" class="Bound">l1</a> <a id="1374" class="Symbol">(</a><a id="1375" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="1377" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1326" class="Bound">l2</a><a id="1379" class="Symbol">)</a>

<a id="1382" class="Keyword">module</a> <a id="1389" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1389" class="Module">_</a>
  <a id="1393" class="Symbol">{</a><a id="1394" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1394" class="Bound">l1</a> <a id="1397" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1397" class="Bound">l2</a> <a id="1400" class="Symbol">:</a> <a id="1402" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1407" class="Symbol">}</a> <a id="1409" class="Symbol">(</a><a id="1410" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1410" class="Bound">S</a> <a id="1412" class="Symbol">:</a> <a id="1414" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1200" class="Function">inhabited-finitely-enumerable-subset-ℝ</a> <a id="1453" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1394" class="Bound">l1</a> <a id="1456" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1397" class="Bound">l2</a><a id="1458" class="Symbol">)</a>
  <a id="1462" class="Keyword">where</a>

  <a id="1471" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1471" class="Function">subset-inhabited-finitely-enumerable-subset-ℝ</a> <a id="1517" class="Symbol">:</a> <a id="1519" href="real-numbers.subsets-real-numbers.html#1495" class="Function">subset-ℝ</a> <a id="1528" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1394" class="Bound">l1</a> <a id="1531" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1397" class="Bound">l2</a>
  <a id="1536" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1471" class="Function">subset-inhabited-finitely-enumerable-subset-ℝ</a> <a id="1582" class="Symbol">=</a>
    <a id="1588" href="univalent-combinatorics.inhabited-finitely-enumerable-subtypes.html#1662" class="Function">subtype-inhabited-finitely-enumerable-subtype</a> <a id="1634" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1410" class="Bound">S</a>

  <a id="1639" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1639" class="Function">type-inhabited-finitely-enumerable-subset-ℝ</a> <a id="1683" class="Symbol">:</a> <a id="1685" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1688" class="Symbol">(</a><a id="1689" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1394" class="Bound">l1</a> <a id="1692" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1694" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1699" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1397" class="Bound">l2</a><a id="1701" class="Symbol">)</a>
  <a id="1705" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1639" class="Function">type-inhabited-finitely-enumerable-subset-ℝ</a> <a id="1749" class="Symbol">=</a>
    <a id="1755" href="univalent-combinatorics.inhabited-finitely-enumerable-subtypes.html#1891" class="Function">type-inhabited-finitely-enumerable-subtype</a> <a id="1798" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1410" class="Bound">S</a>

  <a id="1803" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1803" class="Function">is-finitely-enumerable-inhabited-finitely-enumerable-subset-ℝ</a> <a id="1865" class="Symbol">:</a>
    <a id="1871" href="univalent-combinatorics.finitely-enumerable-subtypes.html#1549" class="Function">is-finitely-enumerable-subtype</a> <a id="1902" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1471" class="Function">subset-inhabited-finitely-enumerable-subset-ℝ</a>
  <a id="1950" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1803" class="Function">is-finitely-enumerable-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2012" class="Symbol">=</a>
    <a id="2018" href="univalent-combinatorics.inhabited-finitely-enumerable-subtypes.html#2249" class="Function">is-finitely-enumerable-type-inhabited-finitely-enumerable-subtype</a> <a id="2084" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1410" class="Bound">S</a>

  <a id="2089" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2089" class="Function">inclusion-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2138" class="Symbol">:</a>
    <a id="2144" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1639" class="Function">type-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2188" class="Symbol">→</a> <a id="2190" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="2192" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1397" class="Bound">l2</a>
  <a id="2197" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2089" class="Function">inclusion-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2246" class="Symbol">=</a>
    <a id="2252" href="foundation-core.subtypes.html#1842" class="Function">inclusion-subtype</a> <a id="2270" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1471" class="Function">subset-inhabited-finitely-enumerable-subset-ℝ</a>

  <a id="2319" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2319" class="Function">is-inhabited-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2371" class="Symbol">:</a>
    <a id="2377" href="foundation.inhabited-types.html#1345" class="Function">is-inhabited</a> <a id="2390" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1639" class="Function">type-inhabited-finitely-enumerable-subset-ℝ</a>
  <a id="2436" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2319" class="Function">is-inhabited-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2488" class="Symbol">=</a>
    <a id="2494" href="univalent-combinatorics.inhabited-finitely-enumerable-subtypes.html#2062" class="Function">is-inhabited-type-inhabited-finitely-enumerable-subtype</a> <a id="2550" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1410" class="Bound">S</a>
</pre>
## Properties

### The elementwise negation of an inhabited finitely enumerable subset of real numbers

<pre class="Agda"><a id="neg-inhabited-finitely-enumerable-subset-ℝ"></a><a id="2669" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2669" class="Function">neg-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2712" class="Symbol">:</a>
  <a id="2716" class="Symbol">{</a><a id="2717" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2717" class="Bound">l1</a> <a id="2720" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2720" class="Bound">l2</a> <a id="2723" class="Symbol">:</a> <a id="2725" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2730" class="Symbol">}</a> <a id="2732" class="Symbol">→</a>
  <a id="2736" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1200" class="Function">inhabited-finitely-enumerable-subset-ℝ</a> <a id="2775" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2717" class="Bound">l1</a> <a id="2778" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2720" class="Bound">l2</a> <a id="2781" class="Symbol">→</a>
  <a id="2785" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1200" class="Function">inhabited-finitely-enumerable-subset-ℝ</a> <a id="2824" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2717" class="Bound">l1</a> <a id="2827" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2720" class="Bound">l2</a>
<a id="2830" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2669" class="Function">neg-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2873" class="Symbol">(</a><a id="2874" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2874" class="Bound">S</a> <a id="2876" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2878" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2878" class="Bound">|S|</a><a id="2881" class="Symbol">)</a> <a id="2883" class="Symbol">=</a>
  <a id="2887" class="Symbol">(</a> <a id="2889" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#2071" class="Function">neg-finitely-enumerable-subset-ℝ</a> <a id="2922" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2874" class="Bound">S</a> <a id="2924" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="2930" href="foundation.inhabited-types.html#6262" class="Function">map-is-inhabited</a>
      <a id="2953" class="Symbol">(</a> <a id="2955" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a>
        <a id="2973" class="Symbol">(</a> <a id="2975" href="foundation.subtypes.html#4178" class="Function">equiv-precomp-equiv-type-subtype</a>
          <a id="3018" class="Symbol">(</a> <a id="3020" href="foundation.involutions.html#2083" class="Function">equiv-is-involution</a> <a id="3040" href="real-numbers.negation-real-numbers.html#3138" class="Function">neg-neg-ℝ</a><a id="3049" class="Symbol">)</a>
          <a id="3061" class="Symbol">(</a> <a id="3063" href="real-numbers.finitely-enumerable-subsets-real-numbers.html#1247" class="Function">subset-finitely-enumerable-subset-ℝ</a> <a id="3099" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2874" class="Bound">S</a><a id="3100" class="Symbol">)))</a>
      <a id="3110" class="Symbol">(</a> <a id="3112" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2878" class="Bound">|S|</a><a id="3115" class="Symbol">))</a>
</pre>