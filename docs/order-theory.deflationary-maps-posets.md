# Deflationary maps on a poset

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="order-theory.deflationary-maps-posets.html" class="Module">order-theory.deflationary-maps-posets</a> <a id="86" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="142" class="Keyword">open</a> <a id="147" class="Keyword">import</a> <a id="154" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="order-theory.deflationary-maps-preorders.html" class="Module">order-theory.deflationary-maps-preorders</a>
<a id="347" class="Keyword">open</a> <a id="352" class="Keyword">import</a> <a id="359" href="order-theory.order-preserving-maps-posets.html" class="Module">order-theory.order-preserving-maps-posets</a>
<a id="401" class="Keyword">open</a> <a id="406" class="Keyword">import</a> <a id="413" href="order-theory.posets.html" class="Module">order-theory.posets</a>
</pre>
</details>

## Idea

A map $f : P → P$ on a [poset](order-theory.posets.md) $P$ is said to be a
{{#concept "deflationary map" Disambiguation="poset" Agda=deflationary-map-Poset}}
if the inequality

$$
  f(x) ≤ x
$$

holds for any element $x : P$. In other words, a map on a poset is deflationary
precisely when the map on its underlying [preorder](order-theory.preorders.md)
is [deflationary](order-theory.deflationary-maps-preorders.md). If $f$ is also
[order preserving](order-theory.order-preserving-maps-posets.md) we say that $f$
is a
{{#concept "deflationary morphism" Disambiguation="poset" Agda=deflationary-hom-Poset}}.

## Definitions

### The predicate of being a deflationary map

<pre class="Agda"><a id="1139" class="Keyword">module</a> <a id="1146" href="order-theory.deflationary-maps-posets.html#1146" class="Module">_</a>
  <a id="1150" class="Symbol">{</a><a id="1151" href="order-theory.deflationary-maps-posets.html#1151" class="Bound">l1</a> <a id="1154" href="order-theory.deflationary-maps-posets.html#1154" class="Bound">l2</a> <a id="1157" class="Symbol">:</a> <a id="1159" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1164" class="Symbol">}</a> <a id="1166" class="Symbol">(</a><a id="1167" href="order-theory.deflationary-maps-posets.html#1167" class="Bound">P</a> <a id="1169" class="Symbol">:</a> <a id="1171" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1177" href="order-theory.deflationary-maps-posets.html#1151" class="Bound">l1</a> <a id="1180" href="order-theory.deflationary-maps-posets.html#1154" class="Bound">l2</a><a id="1182" class="Symbol">)</a> <a id="1184" class="Symbol">(</a><a id="1185" href="order-theory.deflationary-maps-posets.html#1185" class="Bound">f</a> <a id="1187" class="Symbol">:</a> <a id="1189" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="1200" href="order-theory.deflationary-maps-posets.html#1167" class="Bound">P</a> <a id="1202" class="Symbol">→</a> <a id="1204" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="1215" href="order-theory.deflationary-maps-posets.html#1167" class="Bound">P</a><a id="1216" class="Symbol">)</a>
  <a id="1220" class="Keyword">where</a>

  <a id="1229" href="order-theory.deflationary-maps-posets.html#1229" class="Function">is-deflationary-prop-map-Poset</a> <a id="1260" class="Symbol">:</a>
    <a id="1266" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1271" class="Symbol">(</a><a id="1272" href="order-theory.deflationary-maps-posets.html#1151" class="Bound">l1</a> <a id="1275" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1277" href="order-theory.deflationary-maps-posets.html#1154" class="Bound">l2</a><a id="1279" class="Symbol">)</a>
  <a id="1283" href="order-theory.deflationary-maps-posets.html#1229" class="Function">is-deflationary-prop-map-Poset</a> <a id="1314" class="Symbol">=</a>
    <a id="1320" href="order-theory.deflationary-maps-preorders.html#1026" class="Function">is-deflationary-prop-map-Preorder</a> <a id="1354" class="Symbol">(</a><a id="1355" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1370" href="order-theory.deflationary-maps-posets.html#1167" class="Bound">P</a><a id="1371" class="Symbol">)</a> <a id="1373" href="order-theory.deflationary-maps-posets.html#1185" class="Bound">f</a>

  <a id="1378" href="order-theory.deflationary-maps-posets.html#1378" class="Function">is-deflationary-map-Poset</a> <a id="1404" class="Symbol">:</a>
    <a id="1410" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1413" class="Symbol">(</a><a id="1414" href="order-theory.deflationary-maps-posets.html#1151" class="Bound">l1</a> <a id="1417" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1419" href="order-theory.deflationary-maps-posets.html#1154" class="Bound">l2</a><a id="1421" class="Symbol">)</a>
  <a id="1425" href="order-theory.deflationary-maps-posets.html#1378" class="Function">is-deflationary-map-Poset</a> <a id="1451" class="Symbol">=</a>
    <a id="1457" href="order-theory.deflationary-maps-preorders.html#1187" class="Function">is-deflationary-map-Preorder</a> <a id="1486" class="Symbol">(</a><a id="1487" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1502" href="order-theory.deflationary-maps-posets.html#1167" class="Bound">P</a><a id="1503" class="Symbol">)</a> <a id="1505" href="order-theory.deflationary-maps-posets.html#1185" class="Bound">f</a>

  <a id="1510" href="order-theory.deflationary-maps-posets.html#1510" class="Function">is-prop-is-deflationary-map-Poset</a> <a id="1544" class="Symbol">:</a>
    <a id="1550" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1558" href="order-theory.deflationary-maps-posets.html#1378" class="Function">is-deflationary-map-Poset</a>
  <a id="1586" href="order-theory.deflationary-maps-posets.html#1510" class="Function">is-prop-is-deflationary-map-Poset</a> <a id="1620" class="Symbol">=</a>
    <a id="1626" href="order-theory.deflationary-maps-preorders.html#1319" class="Function">is-prop-is-deflationary-map-Preorder</a> <a id="1663" class="Symbol">(</a><a id="1664" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1679" href="order-theory.deflationary-maps-posets.html#1167" class="Bound">P</a><a id="1680" class="Symbol">)</a> <a id="1682" href="order-theory.deflationary-maps-posets.html#1185" class="Bound">f</a>
</pre>
### The type of deflationary maps on a poset

<pre class="Agda"><a id="1743" class="Keyword">module</a> <a id="1750" href="order-theory.deflationary-maps-posets.html#1750" class="Module">_</a>
  <a id="1754" class="Symbol">{</a><a id="1755" href="order-theory.deflationary-maps-posets.html#1755" class="Bound">l1</a> <a id="1758" href="order-theory.deflationary-maps-posets.html#1758" class="Bound">l2</a> <a id="1761" class="Symbol">:</a> <a id="1763" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1768" class="Symbol">}</a> <a id="1770" class="Symbol">(</a><a id="1771" href="order-theory.deflationary-maps-posets.html#1771" class="Bound">P</a> <a id="1773" class="Symbol">:</a> <a id="1775" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1781" href="order-theory.deflationary-maps-posets.html#1755" class="Bound">l1</a> <a id="1784" href="order-theory.deflationary-maps-posets.html#1758" class="Bound">l2</a><a id="1786" class="Symbol">)</a>
  <a id="1790" class="Keyword">where</a>

  <a id="1799" href="order-theory.deflationary-maps-posets.html#1799" class="Function">deflationary-map-Poset</a> <a id="1822" class="Symbol">:</a>
    <a id="1828" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1831" class="Symbol">(</a><a id="1832" href="order-theory.deflationary-maps-posets.html#1755" class="Bound">l1</a> <a id="1835" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1837" href="order-theory.deflationary-maps-posets.html#1758" class="Bound">l2</a><a id="1839" class="Symbol">)</a>
  <a id="1843" href="order-theory.deflationary-maps-posets.html#1799" class="Function">deflationary-map-Poset</a> <a id="1866" class="Symbol">=</a>
    <a id="1872" href="order-theory.deflationary-maps-preorders.html#1617" class="Function">deflationary-map-Preorder</a> <a id="1898" class="Symbol">(</a><a id="1899" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1914" href="order-theory.deflationary-maps-posets.html#1771" class="Bound">P</a><a id="1915" class="Symbol">)</a>

<a id="1918" class="Keyword">module</a> <a id="1925" href="order-theory.deflationary-maps-posets.html#1925" class="Module">_</a>
  <a id="1929" class="Symbol">{</a><a id="1930" href="order-theory.deflationary-maps-posets.html#1930" class="Bound">l1</a> <a id="1933" href="order-theory.deflationary-maps-posets.html#1933" class="Bound">l2</a> <a id="1936" class="Symbol">:</a> <a id="1938" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1943" class="Symbol">}</a> <a id="1945" class="Symbol">(</a><a id="1946" href="order-theory.deflationary-maps-posets.html#1946" class="Bound">P</a> <a id="1948" class="Symbol">:</a> <a id="1950" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1956" href="order-theory.deflationary-maps-posets.html#1930" class="Bound">l1</a> <a id="1959" href="order-theory.deflationary-maps-posets.html#1933" class="Bound">l2</a><a id="1961" class="Symbol">)</a> <a id="1963" class="Symbol">(</a><a id="1964" href="order-theory.deflationary-maps-posets.html#1964" class="Bound">f</a> <a id="1966" class="Symbol">:</a> <a id="1968" href="order-theory.deflationary-maps-posets.html#1799" class="Function">deflationary-map-Poset</a> <a id="1991" href="order-theory.deflationary-maps-posets.html#1946" class="Bound">P</a><a id="1992" class="Symbol">)</a>
  <a id="1996" class="Keyword">where</a>

  <a id="2005" href="order-theory.deflationary-maps-posets.html#2005" class="Function">map-deflationary-map-Poset</a> <a id="2032" class="Symbol">:</a>
    <a id="2038" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="2049" href="order-theory.deflationary-maps-posets.html#1946" class="Bound">P</a> <a id="2051" class="Symbol">→</a> <a id="2053" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="2064" href="order-theory.deflationary-maps-posets.html#1946" class="Bound">P</a>
  <a id="2068" href="order-theory.deflationary-maps-posets.html#2005" class="Function">map-deflationary-map-Poset</a> <a id="2095" class="Symbol">=</a>
    <a id="2101" href="order-theory.deflationary-maps-preorders.html#1841" class="Function">map-deflationary-map-Preorder</a> <a id="2131" class="Symbol">(</a><a id="2132" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="2147" href="order-theory.deflationary-maps-posets.html#1946" class="Bound">P</a><a id="2148" class="Symbol">)</a> <a id="2150" href="order-theory.deflationary-maps-posets.html#1964" class="Bound">f</a>

  <a id="2155" href="order-theory.deflationary-maps-posets.html#2155" class="Function">is-deflationary-deflationary-map-Poset</a> <a id="2194" class="Symbol">:</a>
    <a id="2200" href="order-theory.deflationary-maps-posets.html#1378" class="Function">is-deflationary-map-Poset</a> <a id="2226" href="order-theory.deflationary-maps-posets.html#1946" class="Bound">P</a> <a id="2228" href="order-theory.deflationary-maps-posets.html#2005" class="Function">map-deflationary-map-Poset</a>
  <a id="2257" href="order-theory.deflationary-maps-posets.html#2155" class="Function">is-deflationary-deflationary-map-Poset</a> <a id="2296" class="Symbol">=</a>
    <a id="2302" href="order-theory.deflationary-maps-preorders.html#1958" class="Function">is-deflationary-deflationary-map-Preorder</a> <a id="2344" class="Symbol">(</a><a id="2345" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="2360" href="order-theory.deflationary-maps-posets.html#1946" class="Bound">P</a><a id="2361" class="Symbol">)</a> <a id="2363" href="order-theory.deflationary-maps-posets.html#1964" class="Bound">f</a>
</pre>
### The predicate on order preserving maps of being deflationary

<pre class="Agda"><a id="2444" class="Keyword">module</a> <a id="2451" href="order-theory.deflationary-maps-posets.html#2451" class="Module">_</a>
  <a id="2455" class="Symbol">{</a><a id="2456" href="order-theory.deflationary-maps-posets.html#2456" class="Bound">l1</a> <a id="2459" href="order-theory.deflationary-maps-posets.html#2459" class="Bound">l2</a> <a id="2462" class="Symbol">:</a> <a id="2464" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2469" class="Symbol">}</a> <a id="2471" class="Symbol">(</a><a id="2472" href="order-theory.deflationary-maps-posets.html#2472" class="Bound">P</a> <a id="2474" class="Symbol">:</a> <a id="2476" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="2482" href="order-theory.deflationary-maps-posets.html#2456" class="Bound">l1</a> <a id="2485" href="order-theory.deflationary-maps-posets.html#2459" class="Bound">l2</a><a id="2487" class="Symbol">)</a> <a id="2489" class="Symbol">(</a><a id="2490" href="order-theory.deflationary-maps-posets.html#2490" class="Bound">f</a> <a id="2492" class="Symbol">:</a> <a id="2494" href="order-theory.order-preserving-maps-posets.html#1641" class="Function">hom-Poset</a> <a id="2504" href="order-theory.deflationary-maps-posets.html#2472" class="Bound">P</a> <a id="2506" href="order-theory.deflationary-maps-posets.html#2472" class="Bound">P</a><a id="2507" class="Symbol">)</a>
  <a id="2511" class="Keyword">where</a>

  <a id="2520" href="order-theory.deflationary-maps-posets.html#2520" class="Function">is-deflationary-prop-hom-Poset</a> <a id="2551" class="Symbol">:</a> <a id="2553" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2558" class="Symbol">(</a><a id="2559" href="order-theory.deflationary-maps-posets.html#2456" class="Bound">l1</a> <a id="2562" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2564" href="order-theory.deflationary-maps-posets.html#2459" class="Bound">l2</a><a id="2566" class="Symbol">)</a>
  <a id="2570" href="order-theory.deflationary-maps-posets.html#2520" class="Function">is-deflationary-prop-hom-Poset</a> <a id="2601" class="Symbol">=</a>
    <a id="2607" href="order-theory.deflationary-maps-preorders.html#2284" class="Function">is-deflationary-prop-hom-Preorder</a> <a id="2641" class="Symbol">(</a><a id="2642" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="2657" href="order-theory.deflationary-maps-posets.html#2472" class="Bound">P</a><a id="2658" class="Symbol">)</a> <a id="2660" href="order-theory.deflationary-maps-posets.html#2490" class="Bound">f</a>

  <a id="2665" href="order-theory.deflationary-maps-posets.html#2665" class="Function">is-deflationary-hom-Poset</a> <a id="2691" class="Symbol">:</a> <a id="2693" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2696" class="Symbol">(</a><a id="2697" href="order-theory.deflationary-maps-posets.html#2456" class="Bound">l1</a> <a id="2700" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2702" href="order-theory.deflationary-maps-posets.html#2459" class="Bound">l2</a><a id="2704" class="Symbol">)</a>
  <a id="2708" href="order-theory.deflationary-maps-posets.html#2665" class="Function">is-deflationary-hom-Poset</a> <a id="2734" class="Symbol">=</a>
    <a id="2740" href="order-theory.deflationary-maps-preorders.html#2441" class="Function">is-deflationary-hom-Preorder</a> <a id="2769" class="Symbol">(</a><a id="2770" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="2785" href="order-theory.deflationary-maps-posets.html#2472" class="Bound">P</a><a id="2786" class="Symbol">)</a> <a id="2788" href="order-theory.deflationary-maps-posets.html#2490" class="Bound">f</a>

  <a id="2793" href="order-theory.deflationary-maps-posets.html#2793" class="Function">is-prop-is-deflationary-hom-Poset</a> <a id="2827" class="Symbol">:</a>
    <a id="2833" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2841" href="order-theory.deflationary-maps-posets.html#2665" class="Function">is-deflationary-hom-Poset</a>
  <a id="2869" href="order-theory.deflationary-maps-posets.html#2793" class="Function">is-prop-is-deflationary-hom-Poset</a> <a id="2903" class="Symbol">=</a>
    <a id="2909" href="order-theory.deflationary-maps-preorders.html#2581" class="Function">is-prop-is-deflationary-hom-Preorder</a> <a id="2946" class="Symbol">(</a><a id="2947" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="2962" href="order-theory.deflationary-maps-posets.html#2472" class="Bound">P</a><a id="2963" class="Symbol">)</a> <a id="2965" href="order-theory.deflationary-maps-posets.html#2490" class="Bound">f</a>
</pre>
### The type of deflationary morphisms on a poset

<pre class="Agda"><a id="3031" class="Keyword">module</a> <a id="3038" href="order-theory.deflationary-maps-posets.html#3038" class="Module">_</a>
  <a id="3042" class="Symbol">{</a><a id="3043" href="order-theory.deflationary-maps-posets.html#3043" class="Bound">l1</a> <a id="3046" href="order-theory.deflationary-maps-posets.html#3046" class="Bound">l2</a> <a id="3049" class="Symbol">:</a> <a id="3051" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3056" class="Symbol">}</a> <a id="3058" class="Symbol">(</a><a id="3059" href="order-theory.deflationary-maps-posets.html#3059" class="Bound">P</a> <a id="3061" class="Symbol">:</a> <a id="3063" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="3069" href="order-theory.deflationary-maps-posets.html#3043" class="Bound">l1</a> <a id="3072" href="order-theory.deflationary-maps-posets.html#3046" class="Bound">l2</a><a id="3074" class="Symbol">)</a>
  <a id="3078" class="Keyword">where</a>

  <a id="3087" href="order-theory.deflationary-maps-posets.html#3087" class="Function">deflationary-hom-Poset</a> <a id="3110" class="Symbol">:</a> <a id="3112" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3115" class="Symbol">(</a><a id="3116" href="order-theory.deflationary-maps-posets.html#3043" class="Bound">l1</a> <a id="3119" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3121" href="order-theory.deflationary-maps-posets.html#3046" class="Bound">l2</a><a id="3123" class="Symbol">)</a>
  <a id="3127" href="order-theory.deflationary-maps-posets.html#3087" class="Function">deflationary-hom-Poset</a> <a id="3150" class="Symbol">=</a>
    <a id="3156" href="order-theory.deflationary-maps-preorders.html#2896" class="Function">deflationary-hom-Preorder</a> <a id="3182" class="Symbol">(</a><a id="3183" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="3198" href="order-theory.deflationary-maps-posets.html#3059" class="Bound">P</a><a id="3199" class="Symbol">)</a>

<a id="3202" class="Keyword">module</a> <a id="3209" href="order-theory.deflationary-maps-posets.html#3209" class="Module">_</a>
  <a id="3213" class="Symbol">{</a><a id="3214" href="order-theory.deflationary-maps-posets.html#3214" class="Bound">l1</a> <a id="3217" href="order-theory.deflationary-maps-posets.html#3217" class="Bound">l2</a> <a id="3220" class="Symbol">:</a> <a id="3222" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3227" class="Symbol">}</a> <a id="3229" class="Symbol">(</a><a id="3230" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a> <a id="3232" class="Symbol">:</a> <a id="3234" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="3240" href="order-theory.deflationary-maps-posets.html#3214" class="Bound">l1</a> <a id="3243" href="order-theory.deflationary-maps-posets.html#3217" class="Bound">l2</a><a id="3245" class="Symbol">)</a> <a id="3247" class="Symbol">(</a><a id="3248" href="order-theory.deflationary-maps-posets.html#3248" class="Bound">f</a> <a id="3250" class="Symbol">:</a> <a id="3252" href="order-theory.deflationary-maps-posets.html#3087" class="Function">deflationary-hom-Poset</a> <a id="3275" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a><a id="3276" class="Symbol">)</a>
  <a id="3280" class="Keyword">where</a>

  <a id="3289" href="order-theory.deflationary-maps-posets.html#3289" class="Function">hom-deflationary-hom-Poset</a> <a id="3316" class="Symbol">:</a>
    <a id="3322" href="order-theory.order-preserving-maps-posets.html#1641" class="Function">hom-Poset</a> <a id="3332" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a> <a id="3334" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a>
  <a id="3338" href="order-theory.deflationary-maps-posets.html#3289" class="Function">hom-deflationary-hom-Poset</a> <a id="3365" class="Symbol">=</a>
    <a id="3371" href="order-theory.deflationary-maps-preorders.html#3116" class="Function">hom-deflationary-hom-Preorder</a> <a id="3401" class="Symbol">(</a><a id="3402" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="3417" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a><a id="3418" class="Symbol">)</a> <a id="3420" href="order-theory.deflationary-maps-posets.html#3248" class="Bound">f</a>

  <a id="3425" href="order-theory.deflationary-maps-posets.html#3425" class="Function">map-deflationary-hom-Poset</a> <a id="3452" class="Symbol">:</a>
    <a id="3458" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="3469" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a> <a id="3471" class="Symbol">→</a> <a id="3473" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="3484" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a>
  <a id="3488" href="order-theory.deflationary-maps-posets.html#3425" class="Function">map-deflationary-hom-Poset</a> <a id="3515" class="Symbol">=</a>
    <a id="3521" href="order-theory.deflationary-maps-preorders.html#3216" class="Function">map-deflationary-hom-Preorder</a> <a id="3551" class="Symbol">(</a><a id="3552" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="3567" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a><a id="3568" class="Symbol">)</a> <a id="3570" href="order-theory.deflationary-maps-posets.html#3248" class="Bound">f</a>

  <a id="3575" href="order-theory.deflationary-maps-posets.html#3575" class="Function">preserves-order-deflationary-hom-Poset</a> <a id="3614" class="Symbol">:</a>
    <a id="3620" href="order-theory.order-preserving-maps-posets.html#1086" class="Function">preserves-order-Poset</a> <a id="3642" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a> <a id="3644" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a> <a id="3646" href="order-theory.deflationary-maps-posets.html#3425" class="Function">map-deflationary-hom-Poset</a>
  <a id="3675" href="order-theory.deflationary-maps-posets.html#3575" class="Function">preserves-order-deflationary-hom-Poset</a> <a id="3714" class="Symbol">=</a>
    <a id="3720" href="order-theory.deflationary-maps-preorders.html#3378" class="Function">preserves-order-deflationary-hom-Preorder</a> <a id="3762" class="Symbol">(</a><a id="3763" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="3778" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a><a id="3779" class="Symbol">)</a> <a id="3781" href="order-theory.deflationary-maps-posets.html#3248" class="Bound">f</a>

  <a id="3786" href="order-theory.deflationary-maps-posets.html#3786" class="Function">is-deflationary-deflationary-hom-Poset</a> <a id="3825" class="Symbol">:</a>
    <a id="3831" href="order-theory.deflationary-maps-posets.html#1378" class="Function">is-deflationary-map-Poset</a> <a id="3857" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a> <a id="3859" href="order-theory.deflationary-maps-posets.html#3425" class="Function">map-deflationary-hom-Poset</a>
  <a id="3888" href="order-theory.deflationary-maps-posets.html#3786" class="Function">is-deflationary-deflationary-hom-Poset</a> <a id="3927" class="Symbol">=</a>
    <a id="3933" href="order-theory.deflationary-maps-preorders.html#3601" class="Function">is-deflationary-deflationary-hom-Preorder</a> <a id="3975" class="Symbol">(</a><a id="3976" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="3991" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a><a id="3992" class="Symbol">)</a> <a id="3994" href="order-theory.deflationary-maps-posets.html#3248" class="Bound">f</a>

  <a id="3999" href="order-theory.deflationary-maps-posets.html#3999" class="Function">deflationary-map-deflationary-hom-Poset</a> <a id="4039" class="Symbol">:</a>
    <a id="4045" href="order-theory.deflationary-maps-posets.html#1799" class="Function">deflationary-map-Poset</a> <a id="4068" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a>
  <a id="4072" href="order-theory.deflationary-maps-posets.html#3999" class="Function">deflationary-map-deflationary-hom-Poset</a> <a id="4112" class="Symbol">=</a>
    <a id="4118" href="order-theory.deflationary-maps-preorders.html#3769" class="Function">deflationary-map-deflationary-hom-Preorder</a> <a id="4161" class="Symbol">(</a><a id="4162" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="4177" href="order-theory.deflationary-maps-posets.html#3230" class="Bound">P</a><a id="4178" class="Symbol">)</a> <a id="4180" href="order-theory.deflationary-maps-posets.html#3248" class="Bound">f</a>
</pre>