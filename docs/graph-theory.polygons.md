# Polygons

<pre class="Agda"><a id="21" class="Keyword">module</a> <a id="28" href="graph-theory.polygons.html" class="Module">graph-theory.polygons</a> <a id="50" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="106" class="Keyword">open</a> <a id="111" class="Keyword">import</a> <a id="118" href="elementary-number-theory.modular-arithmetic.html" class="Module">elementary-number-theory.modular-arithmetic</a>
<a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="foundation.decidable-equality.html" class="Module">foundation.decidable-equality</a>
<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="302" class="Keyword">open</a> <a id="307" class="Keyword">import</a> <a id="314" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a>
<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="foundation.functoriality-propositional-truncation.html" class="Module">foundation.functoriality-propositional-truncation</a>
<a id="402" class="Keyword">open</a> <a id="407" class="Keyword">import</a> <a id="414" href="foundation.mere-equivalences.html" class="Module">foundation.mere-equivalences</a>
<a id="443" class="Keyword">open</a> <a id="448" class="Keyword">import</a> <a id="455" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="471" class="Keyword">open</a> <a id="476" class="Keyword">import</a> <a id="483" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="510" class="Keyword">open</a> <a id="515" class="Keyword">import</a> <a id="522" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>

<a id="550" class="Keyword">open</a> <a id="555" class="Keyword">import</a> <a id="562" href="graph-theory.equivalences-undirected-graphs.html" class="Module">graph-theory.equivalences-undirected-graphs</a>
<a id="606" class="Keyword">open</a> <a id="611" class="Keyword">import</a> <a id="618" href="graph-theory.mere-equivalences-undirected-graphs.html" class="Module">graph-theory.mere-equivalences-undirected-graphs</a>
<a id="667" class="Keyword">open</a> <a id="672" class="Keyword">import</a> <a id="679" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>

<a id="711" class="Keyword">open</a> <a id="716" class="Keyword">import</a> <a id="723" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

## Idea

A **polygon** is an [undirected graph](graph-theory.undirected-graphs.md) that
is [merely equivalent](graph-theory.mere-equivalences-undirected-graphs.md) to a
graph with vertices the underlying type of the
[standard cyclic group](elementary-number-theory.standard-cyclic-groups.md)
`ℤ-Mod k` and an edge from each `x ∈ ℤ-Mod k` to `x+1`. This defines for each
`k ∈ ℕ` the type of all `k`-gons. The type of all `k`-gons is a concrete
presentation of the [dihedral group](group-theory.dihedral-groups.md) `Dₖ`.

## Definition

### Standard polygons

<pre class="Agda"><a id="vertex-standard-polygon-Undirected-Graph"></a><a id="1343" href="graph-theory.polygons.html#1343" class="Function">vertex-standard-polygon-Undirected-Graph</a> <a id="1384" class="Symbol">:</a> <a id="1386" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1388" class="Symbol">→</a> <a id="1390" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1393" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1399" href="graph-theory.polygons.html#1343" class="Function">vertex-standard-polygon-Undirected-Graph</a> <a id="1440" href="graph-theory.polygons.html#1440" class="Bound">k</a> <a id="1442" class="Symbol">=</a> <a id="1444" href="elementary-number-theory.modular-arithmetic.html#2573" class="Function">ℤ-Mod</a> <a id="1450" href="graph-theory.polygons.html#1440" class="Bound">k</a>

<a id="unordered-pair-vertices-standard-polygon-Undirected-Graph"></a><a id="1453" href="graph-theory.polygons.html#1453" class="Function">unordered-pair-vertices-standard-polygon-Undirected-Graph</a> <a id="1511" class="Symbol">:</a> <a id="1513" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1515" class="Symbol">→</a> <a id="1517" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1520" class="Symbol">(</a><a id="1521" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1526" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="1531" class="Symbol">)</a>
<a id="1533" href="graph-theory.polygons.html#1453" class="Function">unordered-pair-vertices-standard-polygon-Undirected-Graph</a> <a id="1591" href="graph-theory.polygons.html#1591" class="Bound">k</a> <a id="1593" class="Symbol">=</a>
  <a id="1597" href="foundation.unordered-pairs.html#2222" class="Function">unordered-pair</a> <a id="1612" class="Symbol">(</a><a id="1613" href="graph-theory.polygons.html#1343" class="Function">vertex-standard-polygon-Undirected-Graph</a> <a id="1654" href="graph-theory.polygons.html#1591" class="Bound">k</a><a id="1655" class="Symbol">)</a>

<a id="edge-standard-polygon-Undirected-Graph"></a><a id="1658" href="graph-theory.polygons.html#1658" class="Function">edge-standard-polygon-Undirected-Graph</a> <a id="1697" class="Symbol">:</a>
  <a id="1701" class="Symbol">(</a><a id="1702" href="graph-theory.polygons.html#1702" class="Bound">k</a> <a id="1704" class="Symbol">:</a> <a id="1706" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1707" class="Symbol">)</a> <a id="1709" class="Symbol">→</a>
  <a id="1713" href="graph-theory.polygons.html#1453" class="Function">unordered-pair-vertices-standard-polygon-Undirected-Graph</a> <a id="1771" href="graph-theory.polygons.html#1702" class="Bound">k</a> <a id="1773" class="Symbol">→</a> <a id="1775" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1778" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1784" href="graph-theory.polygons.html#1658" class="Function">edge-standard-polygon-Undirected-Graph</a> <a id="1823" href="graph-theory.polygons.html#1823" class="Bound">k</a> <a id="1825" href="graph-theory.polygons.html#1825" class="Bound">p</a> <a id="1827" class="Symbol">=</a>
  <a id="1831" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1833" class="Symbol">(</a> <a id="1835" href="foundation.unordered-pairs.html#2595" class="Function">type-unordered-pair</a> <a id="1855" href="graph-theory.polygons.html#1825" class="Bound">p</a><a id="1856" class="Symbol">)</a>
    <a id="1862" class="Symbol">(</a> <a id="1864" class="Symbol">λ</a> <a id="1866" href="graph-theory.polygons.html#1866" class="Bound">x</a> <a id="1868" class="Symbol">→</a>
      <a id="1876" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a>
        <a id="1890" class="Symbol">(</a> <a id="1892" href="foundation.unordered-pairs.html#3321" class="Function">element-unordered-pair</a> <a id="1915" href="graph-theory.polygons.html#1825" class="Bound">p</a><a id="1916" class="Symbol">)</a>
        <a id="1926" class="Symbol">(</a> <a id="1928" href="elementary-number-theory.modular-arithmetic.html#5435" class="Function">succ-ℤ-Mod</a> <a id="1939" href="graph-theory.polygons.html#1823" class="Bound">k</a> <a id="1941" class="Symbol">(</a><a id="1942" href="foundation.unordered-pairs.html#3321" class="Function">element-unordered-pair</a> <a id="1965" href="graph-theory.polygons.html#1825" class="Bound">p</a> <a id="1967" href="graph-theory.polygons.html#1866" class="Bound">x</a><a id="1968" class="Symbol">)))</a>

<a id="standard-polygon-Undirected-Graph"></a><a id="1973" href="graph-theory.polygons.html#1973" class="Function">standard-polygon-Undirected-Graph</a> <a id="2007" class="Symbol">:</a> <a id="2009" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2011" class="Symbol">→</a> <a id="2013" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="2030" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="2036" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2042" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2046" class="Symbol">(</a><a id="2047" href="graph-theory.polygons.html#1973" class="Function">standard-polygon-Undirected-Graph</a> <a id="2081" href="graph-theory.polygons.html#2081" class="Bound">k</a><a id="2082" class="Symbol">)</a> <a id="2084" class="Symbol">=</a>
  <a id="2088" href="graph-theory.polygons.html#1343" class="Function">vertex-standard-polygon-Undirected-Graph</a> <a id="2129" href="graph-theory.polygons.html#2081" class="Bound">k</a>
<a id="2131" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2135" class="Symbol">(</a><a id="2136" href="graph-theory.polygons.html#1973" class="Function">standard-polygon-Undirected-Graph</a> <a id="2170" href="graph-theory.polygons.html#2170" class="Bound">k</a><a id="2171" class="Symbol">)</a> <a id="2173" class="Symbol">=</a>
  <a id="2177" href="graph-theory.polygons.html#1658" class="Function">edge-standard-polygon-Undirected-Graph</a> <a id="2216" href="graph-theory.polygons.html#2170" class="Bound">k</a>
</pre>
### The type of all polygons with `k` vertices

<pre class="Agda"><a id="Polygon"></a><a id="2279" href="graph-theory.polygons.html#2279" class="Function">Polygon</a> <a id="2287" class="Symbol">:</a> <a id="2289" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2291" class="Symbol">→</a> <a id="2293" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2296" class="Symbol">(</a><a id="2297" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2302" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="2307" class="Symbol">)</a>
<a id="2309" href="graph-theory.polygons.html#2279" class="Function">Polygon</a> <a id="2317" href="graph-theory.polygons.html#2317" class="Bound">k</a> <a id="2319" class="Symbol">=</a>
  <a id="2323" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2325" class="Symbol">(</a> <a id="2327" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="2344" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="2350" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="2355" class="Symbol">)</a>
    <a id="2361" class="Symbol">(</a> <a id="2363" href="graph-theory.mere-equivalences-undirected-graphs.html#957" class="Function">mere-equiv-Undirected-Graph</a> <a id="2391" class="Symbol">(</a><a id="2392" href="graph-theory.polygons.html#1973" class="Function">standard-polygon-Undirected-Graph</a> <a id="2426" href="graph-theory.polygons.html#2317" class="Bound">k</a><a id="2427" class="Symbol">))</a>

<a id="2431" class="Keyword">module</a> <a id="2438" href="graph-theory.polygons.html#2438" class="Module">_</a>
  <a id="2442" class="Symbol">(</a><a id="2443" href="graph-theory.polygons.html#2443" class="Bound">k</a> <a id="2445" class="Symbol">:</a> <a id="2447" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2448" class="Symbol">)</a> <a id="2450" class="Symbol">(</a><a id="2451" href="graph-theory.polygons.html#2451" class="Bound">X</a> <a id="2453" class="Symbol">:</a> <a id="2455" href="graph-theory.polygons.html#2279" class="Function">Polygon</a> <a id="2463" href="graph-theory.polygons.html#2443" class="Bound">k</a><a id="2464" class="Symbol">)</a>
  <a id="2468" class="Keyword">where</a>

  <a id="2477" href="graph-theory.polygons.html#2477" class="Function">undirected-graph-Polygon</a> <a id="2502" class="Symbol">:</a> <a id="2504" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="2521" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="2527" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="2535" href="graph-theory.polygons.html#2477" class="Function">undirected-graph-Polygon</a> <a id="2560" class="Symbol">=</a> <a id="2562" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2566" href="graph-theory.polygons.html#2451" class="Bound">X</a>

  <a id="2571" href="graph-theory.polygons.html#2571" class="Function">mere-equiv-Polygon</a> <a id="2590" class="Symbol">:</a>
    <a id="2596" href="graph-theory.mere-equivalences-undirected-graphs.html#957" class="Function">mere-equiv-Undirected-Graph</a>
      <a id="2630" class="Symbol">(</a> <a id="2632" href="graph-theory.polygons.html#1973" class="Function">standard-polygon-Undirected-Graph</a> <a id="2666" href="graph-theory.polygons.html#2443" class="Bound">k</a><a id="2667" class="Symbol">)</a>
      <a id="2675" class="Symbol">(</a> <a id="2677" href="graph-theory.polygons.html#2477" class="Function">undirected-graph-Polygon</a><a id="2701" class="Symbol">)</a>
  <a id="2705" href="graph-theory.polygons.html#2571" class="Function">mere-equiv-Polygon</a> <a id="2724" class="Symbol">=</a> <a id="2726" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2730" href="graph-theory.polygons.html#2451" class="Bound">X</a>

  <a id="2735" href="graph-theory.polygons.html#2735" class="Function">vertex-Polygon</a> <a id="2750" class="Symbol">:</a> <a id="2752" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2755" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="2763" href="graph-theory.polygons.html#2735" class="Function">vertex-Polygon</a> <a id="2778" class="Symbol">=</a> <a id="2780" href="graph-theory.undirected-graphs.html#823" class="Function">vertex-Undirected-Graph</a> <a id="2804" href="graph-theory.polygons.html#2477" class="Function">undirected-graph-Polygon</a>

  <a id="2832" href="graph-theory.polygons.html#2832" class="Function">unordered-pair-vertices-Polygon</a> <a id="2864" class="Symbol">:</a> <a id="2866" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2869" class="Symbol">(</a><a id="2870" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2875" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="2880" class="Symbol">)</a>
  <a id="2884" href="graph-theory.polygons.html#2832" class="Function">unordered-pair-vertices-Polygon</a> <a id="2916" class="Symbol">=</a> <a id="2918" href="foundation.unordered-pairs.html#2222" class="Function">unordered-pair</a> <a id="2933" href="graph-theory.polygons.html#2735" class="Function">vertex-Polygon</a>

  <a id="2951" href="graph-theory.polygons.html#2951" class="Function">edge-Polygon</a> <a id="2964" class="Symbol">:</a> <a id="2966" href="graph-theory.polygons.html#2832" class="Function">unordered-pair-vertices-Polygon</a> <a id="2998" class="Symbol">→</a> <a id="3000" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3003" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="3011" href="graph-theory.polygons.html#2951" class="Function">edge-Polygon</a> <a id="3024" class="Symbol">=</a> <a id="3026" href="graph-theory.undirected-graphs.html#1493" class="Function">edge-Undirected-Graph</a> <a id="3048" href="graph-theory.polygons.html#2477" class="Function">undirected-graph-Polygon</a>

  <a id="3076" href="graph-theory.polygons.html#3076" class="Function">vertex-mere-equiv-Polygon</a> <a id="3102" class="Symbol">:</a> <a id="3104" href="foundation.mere-equivalences.html#960" class="Function">mere-equiv</a> <a id="3115" class="Symbol">(</a><a id="3116" href="elementary-number-theory.modular-arithmetic.html#2573" class="Function">ℤ-Mod</a> <a id="3122" href="graph-theory.polygons.html#2443" class="Bound">k</a><a id="3123" class="Symbol">)</a> <a id="3125" href="graph-theory.polygons.html#2735" class="Function">vertex-Polygon</a>
  <a id="3142" href="graph-theory.polygons.html#3076" class="Function">vertex-mere-equiv-Polygon</a> <a id="3168" class="Symbol">=</a>
    <a id="3174" href="foundation.functoriality-propositional-truncation.html#1256" class="Function">map-trunc-Prop</a>
      <a id="3195" class="Symbol">(</a> <a id="3197" href="graph-theory.equivalences-undirected-graphs.html#1878" class="Function">vertex-equiv-equiv-Undirected-Graph</a>
        <a id="3241" class="Symbol">(</a> <a id="3243" href="graph-theory.polygons.html#1973" class="Function">standard-polygon-Undirected-Graph</a> <a id="3277" href="graph-theory.polygons.html#2443" class="Bound">k</a><a id="3278" class="Symbol">)</a>
        <a id="3288" class="Symbol">(</a> <a id="3290" href="graph-theory.polygons.html#2477" class="Function">undirected-graph-Polygon</a><a id="3314" class="Symbol">))</a>
      <a id="3323" class="Symbol">(</a> <a id="3325" href="graph-theory.polygons.html#2571" class="Function">mere-equiv-Polygon</a><a id="3343" class="Symbol">)</a>

  <a id="3348" href="graph-theory.polygons.html#3348" class="Function">is-finite-vertex-Polygon</a> <a id="3373" class="Symbol">:</a> <a id="3375" href="elementary-number-theory.natural-numbers.html#1482" class="Function">is-nonzero-ℕ</a> <a id="3388" href="graph-theory.polygons.html#2443" class="Bound">k</a> <a id="3390" class="Symbol">→</a> <a id="3392" href="univalent-combinatorics.finite-types.html#2289" class="Function">is-finite</a> <a id="3402" href="graph-theory.polygons.html#2735" class="Function">vertex-Polygon</a>
  <a id="3419" href="graph-theory.polygons.html#3348" class="Function">is-finite-vertex-Polygon</a> <a id="3444" href="graph-theory.polygons.html#3444" class="Bound">H</a> <a id="3446" class="Symbol">=</a>
    <a id="3452" href="univalent-combinatorics.finite-types.html#5200" class="Function">is-finite-mere-equiv</a> <a id="3473" href="graph-theory.polygons.html#3076" class="Function">vertex-mere-equiv-Polygon</a> <a id="3499" class="Symbol">(</a><a id="3500" href="elementary-number-theory.modular-arithmetic.html#4039" class="Function">is-finite-ℤ-Mod</a> <a id="3516" href="graph-theory.polygons.html#3444" class="Bound">H</a><a id="3517" class="Symbol">)</a>

  <a id="3522" href="graph-theory.polygons.html#3522" class="Function">is-set-vertex-Polygon</a> <a id="3544" class="Symbol">:</a> <a id="3546" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="3553" href="graph-theory.polygons.html#2735" class="Function">vertex-Polygon</a>
  <a id="3570" href="graph-theory.polygons.html#3522" class="Function">is-set-vertex-Polygon</a> <a id="3592" class="Symbol">=</a>
    <a id="3598" href="foundation.mere-equivalences.html#2985" class="Function">is-set-mere-equiv&#39;</a> <a id="3617" href="graph-theory.polygons.html#3076" class="Function">vertex-mere-equiv-Polygon</a> <a id="3643" class="Symbol">(</a><a id="3644" href="elementary-number-theory.modular-arithmetic.html#3726" class="Function">is-set-ℤ-Mod</a> <a id="3657" href="graph-theory.polygons.html#2443" class="Bound">k</a><a id="3658" class="Symbol">)</a>

  <a id="3663" href="graph-theory.polygons.html#3663" class="Function">has-decidable-equality-vertex-Polygon</a> <a id="3701" class="Symbol">:</a> <a id="3703" href="foundation.decidable-equality.html#1307" class="Function">has-decidable-equality</a> <a id="3726" href="graph-theory.polygons.html#2735" class="Function">vertex-Polygon</a>
  <a id="3743" href="graph-theory.polygons.html#3663" class="Function">has-decidable-equality-vertex-Polygon</a> <a id="3781" class="Symbol">=</a>
    <a id="3787" href="foundation.mere-equivalences.html#3522" class="Function">has-decidable-equality-mere-equiv&#39;</a>
      <a id="3828" class="Symbol">(</a> <a id="3830" href="graph-theory.polygons.html#3076" class="Function">vertex-mere-equiv-Polygon</a><a id="3855" class="Symbol">)</a>
      <a id="3863" class="Symbol">(</a> <a id="3865" href="elementary-number-theory.modular-arithmetic.html#3224" class="Function">has-decidable-equality-ℤ-Mod</a> <a id="3894" href="graph-theory.polygons.html#2443" class="Bound">k</a><a id="3895" class="Symbol">)</a>
</pre>
## Properties

### The type of vertices of a polygon is a set

<pre class="Agda"><a id="is-set-vertex-standard-polygon-Undirected-Graph"></a><a id="3973" href="graph-theory.polygons.html#3973" class="Function">is-set-vertex-standard-polygon-Undirected-Graph</a> <a id="4021" class="Symbol">:</a>
  <a id="4025" class="Symbol">(</a><a id="4026" href="graph-theory.polygons.html#4026" class="Bound">k</a> <a id="4028" class="Symbol">:</a> <a id="4030" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="4031" class="Symbol">)</a> <a id="4033" class="Symbol">→</a> <a id="4035" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="4042" class="Symbol">(</a><a id="4043" href="graph-theory.polygons.html#1343" class="Function">vertex-standard-polygon-Undirected-Graph</a> <a id="4084" href="graph-theory.polygons.html#4026" class="Bound">k</a><a id="4085" class="Symbol">)</a>
<a id="4087" href="graph-theory.polygons.html#3973" class="Function">is-set-vertex-standard-polygon-Undirected-Graph</a> <a id="4135" href="graph-theory.polygons.html#4135" class="Bound">k</a> <a id="4137" class="Symbol">=</a> <a id="4139" href="elementary-number-theory.modular-arithmetic.html#3726" class="Function">is-set-ℤ-Mod</a> <a id="4152" href="graph-theory.polygons.html#4135" class="Bound">k</a>
</pre>
### Every edge is between distinct points

This remains to be formalized.

### Every polygon is a simple graph

This remains to be formalized.

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}

## External links

- [Cycle graph](https://www.wikidata.org/entity/Q622506) on Wikidata
- [Cycle graph](https://en.wikipedia.org/wiki/Cycle_graph) at Wikipedia
- [Cycle graph](https://mathworld.wolfram.com/CycleGraph.html) at Wolfram
  MathWorld
