# Increasing sequences in partially ordered sets

<pre class="Agda"><a id="59" class="Keyword">module</a> <a id="66" href="order-theory.increasing-sequences-posets.html" class="Module">order-theory.increasing-sequences-posets</a> <a id="107" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="elementary-number-theory.decidable-total-order-natural-numbers.html" class="Module">elementary-number-theory.decidable-total-order-natural-numbers</a>
<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a>
<a id="302" class="Keyword">open</a> <a id="307" class="Keyword">import</a> <a id="314" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="356" class="Keyword">open</a> <a id="361" class="Keyword">import</a> <a id="368" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="400" class="Keyword">open</a> <a id="405" class="Keyword">import</a> <a id="412" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="438" class="Keyword">open</a> <a id="443" class="Keyword">import</a> <a id="450" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="476" class="Keyword">open</a> <a id="481" class="Keyword">import</a> <a id="488" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="512" class="Keyword">open</a> <a id="517" class="Keyword">import</a> <a id="524" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="552" class="Keyword">open</a> <a id="557" class="Keyword">import</a> <a id="564" href="lists.sequences.html" class="Module">lists.sequences</a>

<a id="581" class="Keyword">open</a> <a id="586" class="Keyword">import</a> <a id="593" href="order-theory.order-preserving-maps-posets.html" class="Module">order-theory.order-preserving-maps-posets</a>
<a id="635" class="Keyword">open</a> <a id="640" class="Keyword">import</a> <a id="647" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="667" class="Keyword">open</a> <a id="672" class="Keyword">import</a> <a id="679" href="order-theory.sequences-posets.html" class="Module">order-theory.sequences-posets</a>
<a id="709" class="Keyword">open</a> <a id="714" class="Keyword">import</a> <a id="721" href="order-theory.subposets.html" class="Module">order-theory.subposets</a>
</pre>
</details>

## Idea

A [sequence in a partially ordered set](order-theory.sequences-posets.md) `u` is
{{#concept "increasing" Disambiguation="sequence in a poset" Agda=is-increasing-sequence-Poset}}
if it [preserves](order-theory.order-preserving-maps-posets.md) the
[standard ordering on the natural numbers](elementary-number-theory.inequality-natural-numbers.md)
or, equivalently, if `uₙ ≤ uₙ₊₁` for all `n : ℕ`.

## Definitions

### The predicate of being an increasing sequence in a partially ordered set

<pre class="Agda"><a id="1268" class="Keyword">module</a> <a id="1275" href="order-theory.increasing-sequences-posets.html#1275" class="Module">_</a>
  <a id="1279" class="Symbol">{</a><a id="1280" href="order-theory.increasing-sequences-posets.html#1280" class="Bound">l1</a> <a id="1283" href="order-theory.increasing-sequences-posets.html#1283" class="Bound">l2</a> <a id="1286" class="Symbol">:</a> <a id="1288" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1293" class="Symbol">}</a> <a id="1295" class="Symbol">(</a><a id="1296" href="order-theory.increasing-sequences-posets.html#1296" class="Bound">P</a> <a id="1298" class="Symbol">:</a> <a id="1300" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1306" href="order-theory.increasing-sequences-posets.html#1280" class="Bound">l1</a> <a id="1309" href="order-theory.increasing-sequences-posets.html#1283" class="Bound">l2</a><a id="1311" class="Symbol">)</a> <a id="1313" class="Symbol">(</a><a id="1314" href="order-theory.increasing-sequences-posets.html#1314" class="Bound">u</a> <a id="1316" class="Symbol">:</a> <a id="1318" href="order-theory.sequences-posets.html#870" class="Function">sequence-type-Poset</a> <a id="1338" href="order-theory.increasing-sequences-posets.html#1296" class="Bound">P</a><a id="1339" class="Symbol">)</a>
  <a id="1343" class="Keyword">where</a>

  <a id="1352" href="order-theory.increasing-sequences-posets.html#1352" class="Function">is-increasing-prop-sequence-Poset</a> <a id="1386" class="Symbol">:</a> <a id="1388" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1393" href="order-theory.increasing-sequences-posets.html#1283" class="Bound">l2</a>
  <a id="1398" href="order-theory.increasing-sequences-posets.html#1352" class="Function">is-increasing-prop-sequence-Poset</a> <a id="1432" class="Symbol">=</a>
    <a id="1438" href="order-theory.order-preserving-maps-posets.html#895" class="Function">preserves-order-prop-Poset</a> <a id="1465" href="elementary-number-theory.inequality-natural-numbers.html#3817" class="Function">ℕ-Poset</a> <a id="1473" href="order-theory.increasing-sequences-posets.html#1296" class="Bound">P</a> <a id="1475" href="order-theory.increasing-sequences-posets.html#1314" class="Bound">u</a>

  <a id="1480" href="order-theory.increasing-sequences-posets.html#1480" class="Function">is-increasing-sequence-Poset</a> <a id="1509" class="Symbol">:</a> <a id="1511" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1514" href="order-theory.increasing-sequences-posets.html#1283" class="Bound">l2</a>
  <a id="1519" href="order-theory.increasing-sequences-posets.html#1480" class="Function">is-increasing-sequence-Poset</a> <a id="1548" class="Symbol">=</a>
    <a id="1554" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1564" href="order-theory.increasing-sequences-posets.html#1352" class="Function">is-increasing-prop-sequence-Poset</a>
</pre>
### The poset of increasing sequences in a poset

<pre class="Agda"><a id="1661" class="Keyword">module</a> <a id="1668" href="order-theory.increasing-sequences-posets.html#1668" class="Module">_</a>
  <a id="1672" class="Symbol">{</a><a id="1673" href="order-theory.increasing-sequences-posets.html#1673" class="Bound">l1</a> <a id="1676" href="order-theory.increasing-sequences-posets.html#1676" class="Bound">l2</a> <a id="1679" class="Symbol">:</a> <a id="1681" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1686" class="Symbol">}</a> <a id="1688" class="Symbol">(</a><a id="1689" href="order-theory.increasing-sequences-posets.html#1689" class="Bound">P</a> <a id="1691" class="Symbol">:</a> <a id="1693" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1699" href="order-theory.increasing-sequences-posets.html#1673" class="Bound">l1</a> <a id="1702" href="order-theory.increasing-sequences-posets.html#1676" class="Bound">l2</a><a id="1704" class="Symbol">)</a>
  <a id="1708" class="Keyword">where</a>

  <a id="1717" href="order-theory.increasing-sequences-posets.html#1717" class="Function">poset-increasing-sequence-Poset</a> <a id="1749" class="Symbol">:</a> <a id="1751" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1757" class="Symbol">(</a><a id="1758" href="order-theory.increasing-sequences-posets.html#1673" class="Bound">l1</a> <a id="1761" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1763" href="order-theory.increasing-sequences-posets.html#1676" class="Bound">l2</a><a id="1765" class="Symbol">)</a> <a id="1767" href="order-theory.increasing-sequences-posets.html#1676" class="Bound">l2</a>
  <a id="1772" href="order-theory.increasing-sequences-posets.html#1717" class="Function">poset-increasing-sequence-Poset</a> <a id="1804" class="Symbol">=</a>
    <a id="1810" href="order-theory.subposets.html#2092" class="Function">poset-Subposet</a>
      <a id="1831" class="Symbol">(</a> <a id="1833" href="order-theory.sequences-posets.html#2248" class="Function">sequence-Poset</a> <a id="1848" href="order-theory.increasing-sequences-posets.html#1689" class="Bound">P</a><a id="1849" class="Symbol">)</a>
      <a id="1857" class="Symbol">(</a> <a id="1859" href="order-theory.increasing-sequences-posets.html#1352" class="Function">is-increasing-prop-sequence-Poset</a> <a id="1893" href="order-theory.increasing-sequences-posets.html#1689" class="Bound">P</a><a id="1894" class="Symbol">)</a>

  <a id="1899" href="order-theory.increasing-sequences-posets.html#1899" class="Function">increasing-sequence-Poset</a> <a id="1925" class="Symbol">:</a> <a id="1927" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1930" class="Symbol">(</a><a id="1931" href="order-theory.increasing-sequences-posets.html#1673" class="Bound">l1</a> <a id="1934" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1936" href="order-theory.increasing-sequences-posets.html#1676" class="Bound">l2</a><a id="1938" class="Symbol">)</a>
  <a id="1942" href="order-theory.increasing-sequences-posets.html#1899" class="Function">increasing-sequence-Poset</a> <a id="1968" class="Symbol">=</a>
    <a id="1974" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="1985" href="order-theory.increasing-sequences-posets.html#1717" class="Function">poset-increasing-sequence-Poset</a>

  <a id="2020" href="order-theory.increasing-sequences-posets.html#2020" class="Function">seq-increasing-sequence-Poset</a> <a id="2050" class="Symbol">:</a>
    <a id="2056" href="order-theory.increasing-sequences-posets.html#1899" class="Function">increasing-sequence-Poset</a> <a id="2082" class="Symbol">→</a>
    <a id="2088" href="order-theory.sequences-posets.html#870" class="Function">sequence-type-Poset</a> <a id="2108" href="order-theory.increasing-sequences-posets.html#1689" class="Bound">P</a>
  <a id="2112" href="order-theory.increasing-sequences-posets.html#2020" class="Function">seq-increasing-sequence-Poset</a> <a id="2142" class="Symbol">=</a> <a id="2144" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

  <a id="2151" href="order-theory.increasing-sequences-posets.html#2151" class="Function">is-increasing-seq-increasing-sequence-Poset</a> <a id="2195" class="Symbol">:</a>
    <a id="2201" class="Symbol">(</a><a id="2202" href="order-theory.increasing-sequences-posets.html#2202" class="Bound">u</a> <a id="2204" class="Symbol">:</a> <a id="2206" href="order-theory.increasing-sequences-posets.html#1899" class="Function">increasing-sequence-Poset</a><a id="2231" class="Symbol">)</a> <a id="2233" class="Symbol">→</a>
    <a id="2239" href="order-theory.increasing-sequences-posets.html#1480" class="Function">is-increasing-sequence-Poset</a>
      <a id="2274" class="Symbol">(</a> <a id="2276" href="order-theory.increasing-sequences-posets.html#1689" class="Bound">P</a><a id="2277" class="Symbol">)</a>
      <a id="2285" class="Symbol">(</a> <a id="2287" href="order-theory.increasing-sequences-posets.html#2020" class="Function">seq-increasing-sequence-Poset</a> <a id="2317" href="order-theory.increasing-sequences-posets.html#2202" class="Bound">u</a><a id="2318" class="Symbol">)</a>
  <a id="2322" href="order-theory.increasing-sequences-posets.html#2151" class="Function">is-increasing-seq-increasing-sequence-Poset</a> <a id="2366" class="Symbol">=</a> <a id="2368" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>
</pre>
## Properties

### A sequence `u` in a poset is increasing if and only if `uₙ ≤ uₙ₊₁` for all `n : ℕ`

<pre class="Agda"><a id="2488" class="Keyword">module</a> <a id="2495" href="order-theory.increasing-sequences-posets.html#2495" class="Module">_</a>
  <a id="2499" class="Symbol">{</a><a id="2500" href="order-theory.increasing-sequences-posets.html#2500" class="Bound">l1</a> <a id="2503" href="order-theory.increasing-sequences-posets.html#2503" class="Bound">l2</a> <a id="2506" class="Symbol">:</a> <a id="2508" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2513" class="Symbol">}</a> <a id="2515" class="Symbol">(</a><a id="2516" href="order-theory.increasing-sequences-posets.html#2516" class="Bound">P</a> <a id="2518" class="Symbol">:</a> <a id="2520" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="2526" href="order-theory.increasing-sequences-posets.html#2500" class="Bound">l1</a> <a id="2529" href="order-theory.increasing-sequences-posets.html#2503" class="Bound">l2</a><a id="2531" class="Symbol">)</a> <a id="2533" class="Symbol">(</a><a id="2534" href="order-theory.increasing-sequences-posets.html#2534" class="Bound">u</a> <a id="2536" class="Symbol">:</a> <a id="2538" href="order-theory.sequences-posets.html#870" class="Function">sequence-type-Poset</a> <a id="2558" href="order-theory.increasing-sequences-posets.html#2516" class="Bound">P</a><a id="2559" class="Symbol">)</a>
  <a id="2563" class="Keyword">where</a>

  <a id="2572" href="order-theory.increasing-sequences-posets.html#2572" class="Function">is-increasing-leq-succ-sequence-Poset</a> <a id="2610" class="Symbol">:</a>
    <a id="2616" class="Symbol">((</a><a id="2618" href="order-theory.increasing-sequences-posets.html#2618" class="Bound">n</a> <a id="2620" class="Symbol">:</a> <a id="2622" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2623" class="Symbol">)</a> <a id="2625" class="Symbol">→</a> <a id="2627" href="order-theory.posets.html#1514" class="Function">leq-Poset</a> <a id="2637" href="order-theory.increasing-sequences-posets.html#2516" class="Bound">P</a> <a id="2639" class="Symbol">(</a><a id="2640" href="order-theory.increasing-sequences-posets.html#2534" class="Bound">u</a> <a id="2642" href="order-theory.increasing-sequences-posets.html#2618" class="Bound">n</a><a id="2643" class="Symbol">)</a> <a id="2645" class="Symbol">(</a><a id="2646" href="order-theory.increasing-sequences-posets.html#2534" class="Bound">u</a> <a id="2648" class="Symbol">(</a><a id="2649" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2656" href="order-theory.increasing-sequences-posets.html#2618" class="Bound">n</a><a id="2657" class="Symbol">)))</a> <a id="2661" class="Symbol">→</a>
    <a id="2667" href="order-theory.increasing-sequences-posets.html#1480" class="Function">is-increasing-sequence-Poset</a> <a id="2696" href="order-theory.increasing-sequences-posets.html#2516" class="Bound">P</a> <a id="2698" href="order-theory.increasing-sequences-posets.html#2534" class="Bound">u</a>
  <a id="2702" href="order-theory.increasing-sequences-posets.html#2572" class="Function">is-increasing-leq-succ-sequence-Poset</a> <a id="2740" class="Symbol">=</a>
    <a id="2746" href="elementary-number-theory.decidable-total-order-natural-numbers.html#2548" class="Function">preserves-order-ind-ℕ-Poset</a> <a id="2774" href="order-theory.increasing-sequences-posets.html#2516" class="Bound">P</a> <a id="2776" href="order-theory.increasing-sequences-posets.html#2534" class="Bound">u</a>

  <a id="2781" href="order-theory.increasing-sequences-posets.html#2781" class="Function">leq-succ-is-increasing-sequence-Poset</a> <a id="2819" class="Symbol">:</a>
    <a id="2825" href="order-theory.increasing-sequences-posets.html#1480" class="Function">is-increasing-sequence-Poset</a> <a id="2854" href="order-theory.increasing-sequences-posets.html#2516" class="Bound">P</a> <a id="2856" href="order-theory.increasing-sequences-posets.html#2534" class="Bound">u</a> <a id="2858" class="Symbol">→</a>
    <a id="2864" class="Symbol">((</a><a id="2866" href="order-theory.increasing-sequences-posets.html#2866" class="Bound">n</a> <a id="2868" class="Symbol">:</a> <a id="2870" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2871" class="Symbol">)</a> <a id="2873" class="Symbol">→</a> <a id="2875" href="order-theory.posets.html#1514" class="Function">leq-Poset</a> <a id="2885" href="order-theory.increasing-sequences-posets.html#2516" class="Bound">P</a> <a id="2887" class="Symbol">(</a><a id="2888" href="order-theory.increasing-sequences-posets.html#2534" class="Bound">u</a> <a id="2890" href="order-theory.increasing-sequences-posets.html#2866" class="Bound">n</a><a id="2891" class="Symbol">)</a> <a id="2893" class="Symbol">(</a><a id="2894" href="order-theory.increasing-sequences-posets.html#2534" class="Bound">u</a> <a id="2896" class="Symbol">(</a><a id="2897" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2904" href="order-theory.increasing-sequences-posets.html#2866" class="Bound">n</a><a id="2905" class="Symbol">)))</a>
  <a id="2911" href="order-theory.increasing-sequences-posets.html#2781" class="Function">leq-succ-is-increasing-sequence-Poset</a> <a id="2949" href="order-theory.increasing-sequences-posets.html#2949" class="Bound">H</a> <a id="2951" href="order-theory.increasing-sequences-posets.html#2951" class="Bound">n</a> <a id="2953" class="Symbol">=</a>
    <a id="2959" href="order-theory.increasing-sequences-posets.html#2949" class="Bound">H</a> <a id="2961" href="order-theory.increasing-sequences-posets.html#2951" class="Bound">n</a> <a id="2963" class="Symbol">(</a><a id="2964" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2971" href="order-theory.increasing-sequences-posets.html#2951" class="Bound">n</a><a id="2972" class="Symbol">)</a> <a id="2974" class="Symbol">(</a><a id="2975" href="elementary-number-theory.inequality-natural-numbers.html#6410" class="Function">succ-leq-ℕ</a> <a id="2986" href="order-theory.increasing-sequences-posets.html#2951" class="Bound">n</a><a id="2987" class="Symbol">)</a>
</pre>