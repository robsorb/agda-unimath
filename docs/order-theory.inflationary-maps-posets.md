# Inflationary maps on a poset

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="order-theory.inflationary-maps-posets.html" class="Module">order-theory.inflationary-maps-posets</a> <a id="86" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="142" class="Keyword">open</a> <a id="147" class="Keyword">import</a> <a id="154" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="order-theory.inflationary-maps-preorders.html" class="Module">order-theory.inflationary-maps-preorders</a>
<a id="347" class="Keyword">open</a> <a id="352" class="Keyword">import</a> <a id="359" href="order-theory.order-preserving-maps-posets.html" class="Module">order-theory.order-preserving-maps-posets</a>
<a id="401" class="Keyword">open</a> <a id="406" class="Keyword">import</a> <a id="413" href="order-theory.posets.html" class="Module">order-theory.posets</a>
</pre>
</details>

## Idea

A map $f : P → P$ on a [poset](order-theory.posets.md) $P$ is said to be an
{{#concept "inflationary map" Disambiguation="poset" Agda=inflationary-map-Poset}}
if the inequality

$$
  x ≤ f(x)
$$

holds for any element $x : P$. In other words, a map on a poset is inflationary
precisely when the map on its underlying [preorder](order-theory.preorders.md)
is [inflationary](order-theory.inflationary-maps-preorders.md). If $f$ is also
[order preserving](order-theory.order-preserving-maps-posets.md) we say that $f$
is an
{{#concept "inflationary morphism" Disambiguation="poset" Agda=inflationary-hom-Poset}}.

## Definitions

### The predicate of being an inflationary map

<pre class="Agda"><a id="1142" class="Keyword">module</a> <a id="1149" href="order-theory.inflationary-maps-posets.html#1149" class="Module">_</a>
  <a id="1153" class="Symbol">{</a><a id="1154" href="order-theory.inflationary-maps-posets.html#1154" class="Bound">l1</a> <a id="1157" href="order-theory.inflationary-maps-posets.html#1157" class="Bound">l2</a> <a id="1160" class="Symbol">:</a> <a id="1162" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1167" class="Symbol">}</a> <a id="1169" class="Symbol">(</a><a id="1170" href="order-theory.inflationary-maps-posets.html#1170" class="Bound">P</a> <a id="1172" class="Symbol">:</a> <a id="1174" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1180" href="order-theory.inflationary-maps-posets.html#1154" class="Bound">l1</a> <a id="1183" href="order-theory.inflationary-maps-posets.html#1157" class="Bound">l2</a><a id="1185" class="Symbol">)</a> <a id="1187" class="Symbol">(</a><a id="1188" href="order-theory.inflationary-maps-posets.html#1188" class="Bound">f</a> <a id="1190" class="Symbol">:</a> <a id="1192" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="1203" href="order-theory.inflationary-maps-posets.html#1170" class="Bound">P</a> <a id="1205" class="Symbol">→</a> <a id="1207" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="1218" href="order-theory.inflationary-maps-posets.html#1170" class="Bound">P</a><a id="1219" class="Symbol">)</a>
  <a id="1223" class="Keyword">where</a>

  <a id="1232" href="order-theory.inflationary-maps-posets.html#1232" class="Function">is-inflationary-prop-map-Poset</a> <a id="1263" class="Symbol">:</a>
    <a id="1269" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1274" class="Symbol">(</a><a id="1275" href="order-theory.inflationary-maps-posets.html#1154" class="Bound">l1</a> <a id="1278" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1280" href="order-theory.inflationary-maps-posets.html#1157" class="Bound">l2</a><a id="1282" class="Symbol">)</a>
  <a id="1286" href="order-theory.inflationary-maps-posets.html#1232" class="Function">is-inflationary-prop-map-Poset</a> <a id="1317" class="Symbol">=</a>
    <a id="1323" href="order-theory.inflationary-maps-preorders.html#1029" class="Function">is-inflationary-prop-map-Preorder</a> <a id="1357" class="Symbol">(</a><a id="1358" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1373" href="order-theory.inflationary-maps-posets.html#1170" class="Bound">P</a><a id="1374" class="Symbol">)</a> <a id="1376" href="order-theory.inflationary-maps-posets.html#1188" class="Bound">f</a>

  <a id="1381" href="order-theory.inflationary-maps-posets.html#1381" class="Function">is-inflationary-map-Poset</a> <a id="1407" class="Symbol">:</a>
    <a id="1413" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1416" class="Symbol">(</a><a id="1417" href="order-theory.inflationary-maps-posets.html#1154" class="Bound">l1</a> <a id="1420" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1422" href="order-theory.inflationary-maps-posets.html#1157" class="Bound">l2</a><a id="1424" class="Symbol">)</a>
  <a id="1428" href="order-theory.inflationary-maps-posets.html#1381" class="Function">is-inflationary-map-Poset</a> <a id="1454" class="Symbol">=</a>
    <a id="1460" href="order-theory.inflationary-maps-preorders.html#1190" class="Function">is-inflationary-map-Preorder</a> <a id="1489" class="Symbol">(</a><a id="1490" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1505" href="order-theory.inflationary-maps-posets.html#1170" class="Bound">P</a><a id="1506" class="Symbol">)</a> <a id="1508" href="order-theory.inflationary-maps-posets.html#1188" class="Bound">f</a>

  <a id="1513" href="order-theory.inflationary-maps-posets.html#1513" class="Function">is-prop-is-inflationary-map-Poset</a> <a id="1547" class="Symbol">:</a>
    <a id="1553" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1561" href="order-theory.inflationary-maps-posets.html#1381" class="Function">is-inflationary-map-Poset</a>
  <a id="1589" href="order-theory.inflationary-maps-posets.html#1513" class="Function">is-prop-is-inflationary-map-Poset</a> <a id="1623" class="Symbol">=</a>
    <a id="1629" href="order-theory.inflationary-maps-preorders.html#1322" class="Function">is-prop-is-inflationary-map-Preorder</a> <a id="1666" class="Symbol">(</a><a id="1667" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1682" href="order-theory.inflationary-maps-posets.html#1170" class="Bound">P</a><a id="1683" class="Symbol">)</a> <a id="1685" href="order-theory.inflationary-maps-posets.html#1188" class="Bound">f</a>
</pre>
### The type of inflationary maps on a poset

<pre class="Agda"><a id="1746" class="Keyword">module</a> <a id="1753" href="order-theory.inflationary-maps-posets.html#1753" class="Module">_</a>
  <a id="1757" class="Symbol">{</a><a id="1758" href="order-theory.inflationary-maps-posets.html#1758" class="Bound">l1</a> <a id="1761" href="order-theory.inflationary-maps-posets.html#1761" class="Bound">l2</a> <a id="1764" class="Symbol">:</a> <a id="1766" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1771" class="Symbol">}</a> <a id="1773" class="Symbol">(</a><a id="1774" href="order-theory.inflationary-maps-posets.html#1774" class="Bound">P</a> <a id="1776" class="Symbol">:</a> <a id="1778" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1784" href="order-theory.inflationary-maps-posets.html#1758" class="Bound">l1</a> <a id="1787" href="order-theory.inflationary-maps-posets.html#1761" class="Bound">l2</a><a id="1789" class="Symbol">)</a>
  <a id="1793" class="Keyword">where</a>

  <a id="1802" href="order-theory.inflationary-maps-posets.html#1802" class="Function">inflationary-map-Poset</a> <a id="1825" class="Symbol">:</a>
    <a id="1831" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1834" class="Symbol">(</a><a id="1835" href="order-theory.inflationary-maps-posets.html#1758" class="Bound">l1</a> <a id="1838" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1840" href="order-theory.inflationary-maps-posets.html#1761" class="Bound">l2</a><a id="1842" class="Symbol">)</a>
  <a id="1846" href="order-theory.inflationary-maps-posets.html#1802" class="Function">inflationary-map-Poset</a> <a id="1869" class="Symbol">=</a>
    <a id="1875" href="order-theory.inflationary-maps-preorders.html#1620" class="Function">inflationary-map-Preorder</a> <a id="1901" class="Symbol">(</a><a id="1902" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1917" href="order-theory.inflationary-maps-posets.html#1774" class="Bound">P</a><a id="1918" class="Symbol">)</a>

<a id="1921" class="Keyword">module</a> <a id="1928" href="order-theory.inflationary-maps-posets.html#1928" class="Module">_</a>
  <a id="1932" class="Symbol">{</a><a id="1933" href="order-theory.inflationary-maps-posets.html#1933" class="Bound">l1</a> <a id="1936" href="order-theory.inflationary-maps-posets.html#1936" class="Bound">l2</a> <a id="1939" class="Symbol">:</a> <a id="1941" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1946" class="Symbol">}</a> <a id="1948" class="Symbol">(</a><a id="1949" href="order-theory.inflationary-maps-posets.html#1949" class="Bound">P</a> <a id="1951" class="Symbol">:</a> <a id="1953" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1959" href="order-theory.inflationary-maps-posets.html#1933" class="Bound">l1</a> <a id="1962" href="order-theory.inflationary-maps-posets.html#1936" class="Bound">l2</a><a id="1964" class="Symbol">)</a> <a id="1966" class="Symbol">(</a><a id="1967" href="order-theory.inflationary-maps-posets.html#1967" class="Bound">f</a> <a id="1969" class="Symbol">:</a> <a id="1971" href="order-theory.inflationary-maps-posets.html#1802" class="Function">inflationary-map-Poset</a> <a id="1994" href="order-theory.inflationary-maps-posets.html#1949" class="Bound">P</a><a id="1995" class="Symbol">)</a>
  <a id="1999" class="Keyword">where</a>

  <a id="2008" href="order-theory.inflationary-maps-posets.html#2008" class="Function">map-inflationary-map-Poset</a> <a id="2035" class="Symbol">:</a>
    <a id="2041" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="2052" href="order-theory.inflationary-maps-posets.html#1949" class="Bound">P</a> <a id="2054" class="Symbol">→</a> <a id="2056" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="2067" href="order-theory.inflationary-maps-posets.html#1949" class="Bound">P</a>
  <a id="2071" href="order-theory.inflationary-maps-posets.html#2008" class="Function">map-inflationary-map-Poset</a> <a id="2098" class="Symbol">=</a>
    <a id="2104" href="order-theory.inflationary-maps-preorders.html#1844" class="Function">map-inflationary-map-Preorder</a> <a id="2134" class="Symbol">(</a><a id="2135" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="2150" href="order-theory.inflationary-maps-posets.html#1949" class="Bound">P</a><a id="2151" class="Symbol">)</a> <a id="2153" href="order-theory.inflationary-maps-posets.html#1967" class="Bound">f</a>

  <a id="2158" href="order-theory.inflationary-maps-posets.html#2158" class="Function">is-inflationary-inflationary-map-Poset</a> <a id="2197" class="Symbol">:</a>
    <a id="2203" href="order-theory.inflationary-maps-posets.html#1381" class="Function">is-inflationary-map-Poset</a> <a id="2229" href="order-theory.inflationary-maps-posets.html#1949" class="Bound">P</a> <a id="2231" href="order-theory.inflationary-maps-posets.html#2008" class="Function">map-inflationary-map-Poset</a>
  <a id="2260" href="order-theory.inflationary-maps-posets.html#2158" class="Function">is-inflationary-inflationary-map-Poset</a> <a id="2299" class="Symbol">=</a>
    <a id="2305" href="order-theory.inflationary-maps-preorders.html#1961" class="Function">is-inflationary-inflationary-map-Preorder</a> <a id="2347" class="Symbol">(</a><a id="2348" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="2363" href="order-theory.inflationary-maps-posets.html#1949" class="Bound">P</a><a id="2364" class="Symbol">)</a> <a id="2366" href="order-theory.inflationary-maps-posets.html#1967" class="Bound">f</a>
</pre>
### The predicate on order preserving maps of being inflationary

<pre class="Agda"><a id="2447" class="Keyword">module</a> <a id="2454" href="order-theory.inflationary-maps-posets.html#2454" class="Module">_</a>
  <a id="2458" class="Symbol">{</a><a id="2459" href="order-theory.inflationary-maps-posets.html#2459" class="Bound">l1</a> <a id="2462" href="order-theory.inflationary-maps-posets.html#2462" class="Bound">l2</a> <a id="2465" class="Symbol">:</a> <a id="2467" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2472" class="Symbol">}</a> <a id="2474" class="Symbol">(</a><a id="2475" href="order-theory.inflationary-maps-posets.html#2475" class="Bound">P</a> <a id="2477" class="Symbol">:</a> <a id="2479" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="2485" href="order-theory.inflationary-maps-posets.html#2459" class="Bound">l1</a> <a id="2488" href="order-theory.inflationary-maps-posets.html#2462" class="Bound">l2</a><a id="2490" class="Symbol">)</a> <a id="2492" class="Symbol">(</a><a id="2493" href="order-theory.inflationary-maps-posets.html#2493" class="Bound">f</a> <a id="2495" class="Symbol">:</a> <a id="2497" href="order-theory.order-preserving-maps-posets.html#1641" class="Function">hom-Poset</a> <a id="2507" href="order-theory.inflationary-maps-posets.html#2475" class="Bound">P</a> <a id="2509" href="order-theory.inflationary-maps-posets.html#2475" class="Bound">P</a><a id="2510" class="Symbol">)</a>
  <a id="2514" class="Keyword">where</a>

  <a id="2523" href="order-theory.inflationary-maps-posets.html#2523" class="Function">is-inflationary-prop-hom-Poset</a> <a id="2554" class="Symbol">:</a> <a id="2556" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2561" class="Symbol">(</a><a id="2562" href="order-theory.inflationary-maps-posets.html#2459" class="Bound">l1</a> <a id="2565" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2567" href="order-theory.inflationary-maps-posets.html#2462" class="Bound">l2</a><a id="2569" class="Symbol">)</a>
  <a id="2573" href="order-theory.inflationary-maps-posets.html#2523" class="Function">is-inflationary-prop-hom-Poset</a> <a id="2604" class="Symbol">=</a>
    <a id="2610" href="order-theory.inflationary-maps-preorders.html#2287" class="Function">is-inflationary-prop-hom-Preorder</a> <a id="2644" class="Symbol">(</a><a id="2645" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="2660" href="order-theory.inflationary-maps-posets.html#2475" class="Bound">P</a><a id="2661" class="Symbol">)</a> <a id="2663" href="order-theory.inflationary-maps-posets.html#2493" class="Bound">f</a>

  <a id="2668" href="order-theory.inflationary-maps-posets.html#2668" class="Function">is-inflationary-hom-Poset</a> <a id="2694" class="Symbol">:</a> <a id="2696" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2699" class="Symbol">(</a><a id="2700" href="order-theory.inflationary-maps-posets.html#2459" class="Bound">l1</a> <a id="2703" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2705" href="order-theory.inflationary-maps-posets.html#2462" class="Bound">l2</a><a id="2707" class="Symbol">)</a>
  <a id="2711" href="order-theory.inflationary-maps-posets.html#2668" class="Function">is-inflationary-hom-Poset</a> <a id="2737" class="Symbol">=</a>
    <a id="2743" href="order-theory.inflationary-maps-preorders.html#2444" class="Function">is-inflationary-hom-Preorder</a> <a id="2772" class="Symbol">(</a><a id="2773" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="2788" href="order-theory.inflationary-maps-posets.html#2475" class="Bound">P</a><a id="2789" class="Symbol">)</a> <a id="2791" href="order-theory.inflationary-maps-posets.html#2493" class="Bound">f</a>

  <a id="2796" href="order-theory.inflationary-maps-posets.html#2796" class="Function">is-prop-is-inflationary-hom-Poset</a> <a id="2830" class="Symbol">:</a>
    <a id="2836" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2844" href="order-theory.inflationary-maps-posets.html#2668" class="Function">is-inflationary-hom-Poset</a>
  <a id="2872" href="order-theory.inflationary-maps-posets.html#2796" class="Function">is-prop-is-inflationary-hom-Poset</a> <a id="2906" class="Symbol">=</a>
    <a id="2912" href="order-theory.inflationary-maps-preorders.html#2584" class="Function">is-prop-is-inflationary-hom-Preorder</a> <a id="2949" class="Symbol">(</a><a id="2950" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="2965" href="order-theory.inflationary-maps-posets.html#2475" class="Bound">P</a><a id="2966" class="Symbol">)</a> <a id="2968" href="order-theory.inflationary-maps-posets.html#2493" class="Bound">f</a>
</pre>
### The type of inflationary morphisms on a poset

<pre class="Agda"><a id="3034" class="Keyword">module</a> <a id="3041" href="order-theory.inflationary-maps-posets.html#3041" class="Module">_</a>
  <a id="3045" class="Symbol">{</a><a id="3046" href="order-theory.inflationary-maps-posets.html#3046" class="Bound">l1</a> <a id="3049" href="order-theory.inflationary-maps-posets.html#3049" class="Bound">l2</a> <a id="3052" class="Symbol">:</a> <a id="3054" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3059" class="Symbol">}</a> <a id="3061" class="Symbol">(</a><a id="3062" href="order-theory.inflationary-maps-posets.html#3062" class="Bound">P</a> <a id="3064" class="Symbol">:</a> <a id="3066" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="3072" href="order-theory.inflationary-maps-posets.html#3046" class="Bound">l1</a> <a id="3075" href="order-theory.inflationary-maps-posets.html#3049" class="Bound">l2</a><a id="3077" class="Symbol">)</a>
  <a id="3081" class="Keyword">where</a>

  <a id="3090" href="order-theory.inflationary-maps-posets.html#3090" class="Function">inflationary-hom-Poset</a> <a id="3113" class="Symbol">:</a> <a id="3115" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3118" class="Symbol">(</a><a id="3119" href="order-theory.inflationary-maps-posets.html#3046" class="Bound">l1</a> <a id="3122" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3124" href="order-theory.inflationary-maps-posets.html#3049" class="Bound">l2</a><a id="3126" class="Symbol">)</a>
  <a id="3130" href="order-theory.inflationary-maps-posets.html#3090" class="Function">inflationary-hom-Poset</a> <a id="3153" class="Symbol">=</a>
    <a id="3159" href="order-theory.inflationary-maps-preorders.html#2899" class="Function">inflationary-hom-Preorder</a> <a id="3185" class="Symbol">(</a><a id="3186" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="3201" href="order-theory.inflationary-maps-posets.html#3062" class="Bound">P</a><a id="3202" class="Symbol">)</a>

<a id="3205" class="Keyword">module</a> <a id="3212" href="order-theory.inflationary-maps-posets.html#3212" class="Module">_</a>
  <a id="3216" class="Symbol">{</a><a id="3217" href="order-theory.inflationary-maps-posets.html#3217" class="Bound">l1</a> <a id="3220" href="order-theory.inflationary-maps-posets.html#3220" class="Bound">l2</a> <a id="3223" class="Symbol">:</a> <a id="3225" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3230" class="Symbol">}</a> <a id="3232" class="Symbol">(</a><a id="3233" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a> <a id="3235" class="Symbol">:</a> <a id="3237" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="3243" href="order-theory.inflationary-maps-posets.html#3217" class="Bound">l1</a> <a id="3246" href="order-theory.inflationary-maps-posets.html#3220" class="Bound">l2</a><a id="3248" class="Symbol">)</a> <a id="3250" class="Symbol">(</a><a id="3251" href="order-theory.inflationary-maps-posets.html#3251" class="Bound">f</a> <a id="3253" class="Symbol">:</a> <a id="3255" href="order-theory.inflationary-maps-posets.html#3090" class="Function">inflationary-hom-Poset</a> <a id="3278" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a><a id="3279" class="Symbol">)</a>
  <a id="3283" class="Keyword">where</a>

  <a id="3292" href="order-theory.inflationary-maps-posets.html#3292" class="Function">hom-inflationary-hom-Poset</a> <a id="3319" class="Symbol">:</a>
    <a id="3325" href="order-theory.order-preserving-maps-posets.html#1641" class="Function">hom-Poset</a> <a id="3335" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a> <a id="3337" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a>
  <a id="3341" href="order-theory.inflationary-maps-posets.html#3292" class="Function">hom-inflationary-hom-Poset</a> <a id="3368" class="Symbol">=</a>
    <a id="3374" href="order-theory.inflationary-maps-preorders.html#3119" class="Function">hom-inflationary-hom-Preorder</a> <a id="3404" class="Symbol">(</a><a id="3405" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="3420" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a><a id="3421" class="Symbol">)</a> <a id="3423" href="order-theory.inflationary-maps-posets.html#3251" class="Bound">f</a>

  <a id="3428" href="order-theory.inflationary-maps-posets.html#3428" class="Function">map-inflationary-hom-Poset</a> <a id="3455" class="Symbol">:</a>
    <a id="3461" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="3472" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a> <a id="3474" class="Symbol">→</a> <a id="3476" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="3487" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a>
  <a id="3491" href="order-theory.inflationary-maps-posets.html#3428" class="Function">map-inflationary-hom-Poset</a> <a id="3518" class="Symbol">=</a>
    <a id="3524" href="order-theory.inflationary-maps-preorders.html#3219" class="Function">map-inflationary-hom-Preorder</a> <a id="3554" class="Symbol">(</a><a id="3555" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="3570" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a><a id="3571" class="Symbol">)</a> <a id="3573" href="order-theory.inflationary-maps-posets.html#3251" class="Bound">f</a>

  <a id="3578" href="order-theory.inflationary-maps-posets.html#3578" class="Function">preserves-order-inflationary-hom-Poset</a> <a id="3617" class="Symbol">:</a>
    <a id="3623" href="order-theory.order-preserving-maps-posets.html#1086" class="Function">preserves-order-Poset</a> <a id="3645" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a> <a id="3647" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a> <a id="3649" href="order-theory.inflationary-maps-posets.html#3428" class="Function">map-inflationary-hom-Poset</a>
  <a id="3678" href="order-theory.inflationary-maps-posets.html#3578" class="Function">preserves-order-inflationary-hom-Poset</a> <a id="3717" class="Symbol">=</a>
    <a id="3723" href="order-theory.inflationary-maps-preorders.html#3381" class="Function">preserves-order-inflationary-hom-Preorder</a> <a id="3765" class="Symbol">(</a><a id="3766" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="3781" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a><a id="3782" class="Symbol">)</a> <a id="3784" href="order-theory.inflationary-maps-posets.html#3251" class="Bound">f</a>

  <a id="3789" href="order-theory.inflationary-maps-posets.html#3789" class="Function">is-inflationary-inflationary-hom-Poset</a> <a id="3828" class="Symbol">:</a>
    <a id="3834" href="order-theory.inflationary-maps-posets.html#1381" class="Function">is-inflationary-map-Poset</a> <a id="3860" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a> <a id="3862" href="order-theory.inflationary-maps-posets.html#3428" class="Function">map-inflationary-hom-Poset</a>
  <a id="3891" href="order-theory.inflationary-maps-posets.html#3789" class="Function">is-inflationary-inflationary-hom-Poset</a> <a id="3930" class="Symbol">=</a>
    <a id="3936" href="order-theory.inflationary-maps-preorders.html#3604" class="Function">is-inflationary-inflationary-hom-Preorder</a> <a id="3978" class="Symbol">(</a><a id="3979" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="3994" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a><a id="3995" class="Symbol">)</a> <a id="3997" href="order-theory.inflationary-maps-posets.html#3251" class="Bound">f</a>

  <a id="4002" href="order-theory.inflationary-maps-posets.html#4002" class="Function">inflationary-map-inflationary-hom-Poset</a> <a id="4042" class="Symbol">:</a>
    <a id="4048" href="order-theory.inflationary-maps-posets.html#1802" class="Function">inflationary-map-Poset</a> <a id="4071" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a>
  <a id="4075" href="order-theory.inflationary-maps-posets.html#4002" class="Function">inflationary-map-inflationary-hom-Poset</a> <a id="4115" class="Symbol">=</a>
    <a id="4121" href="order-theory.inflationary-maps-preorders.html#3772" class="Function">inflationary-map-inflationary-hom-Preorder</a> <a id="4164" class="Symbol">(</a><a id="4165" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="4180" href="order-theory.inflationary-maps-posets.html#3233" class="Bound">P</a><a id="4181" class="Symbol">)</a> <a id="4183" href="order-theory.inflationary-maps-posets.html#3251" class="Bound">f</a>
</pre>