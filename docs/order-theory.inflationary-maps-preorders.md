# Inflationary maps on a preorder

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="order-theory.inflationary-maps-preorders.html" class="Module">order-theory.inflationary-maps-preorders</a> <a id="92" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="192" class="Keyword">open</a> <a id="197" class="Keyword">import</a> <a id="204" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="228" class="Keyword">open</a> <a id="233" class="Keyword">import</a> <a id="240" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="260" class="Keyword">open</a> <a id="265" class="Keyword">import</a> <a id="272" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="300" class="Keyword">open</a> <a id="305" class="Keyword">import</a> <a id="312" href="order-theory.order-preserving-maps-preorders.html" class="Module">order-theory.order-preserving-maps-preorders</a>
<a id="357" class="Keyword">open</a> <a id="362" class="Keyword">import</a> <a id="369" href="order-theory.preorders.html" class="Module">order-theory.preorders</a>
</pre>
</details>

## Idea

A map $f : P → P$ on a [preorder](order-theory.preorders.md) $P$ is said to be
an
{{#concept "inflationary map" Disambiguation="preorder" Agda=inflationary-map-Preorder}}
if the inequality

$$
  x ≤ f(x)
$$

holds for any element $x : P$. If $f$ is also
[order preserving](order-theory.order-preserving-maps-preorders.md) we say that
$f$ is an
{{#concept "inflationary morphism" Disambiguation="preorder" Agda=inflationary-hom-Preorder}}.

## Definitions

### The predicate of being an inflationary map

<pre class="Agda"><a id="930" class="Keyword">module</a> <a id="937" href="order-theory.inflationary-maps-preorders.html#937" class="Module">_</a>
  <a id="941" class="Symbol">{</a><a id="942" href="order-theory.inflationary-maps-preorders.html#942" class="Bound">l1</a> <a id="945" href="order-theory.inflationary-maps-preorders.html#945" class="Bound">l2</a> <a id="948" class="Symbol">:</a> <a id="950" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="955" class="Symbol">}</a> <a id="957" class="Symbol">(</a><a id="958" href="order-theory.inflationary-maps-preorders.html#958" class="Bound">P</a> <a id="960" class="Symbol">:</a> <a id="962" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="971" href="order-theory.inflationary-maps-preorders.html#942" class="Bound">l1</a> <a id="974" href="order-theory.inflationary-maps-preorders.html#945" class="Bound">l2</a><a id="976" class="Symbol">)</a> <a id="978" class="Symbol">(</a><a id="979" href="order-theory.inflationary-maps-preorders.html#979" class="Bound">f</a> <a id="981" class="Symbol">:</a> <a id="983" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="997" href="order-theory.inflationary-maps-preorders.html#958" class="Bound">P</a> <a id="999" class="Symbol">→</a> <a id="1001" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="1015" href="order-theory.inflationary-maps-preorders.html#958" class="Bound">P</a><a id="1016" class="Symbol">)</a>
  <a id="1020" class="Keyword">where</a>

  <a id="1029" href="order-theory.inflationary-maps-preorders.html#1029" class="Function">is-inflationary-prop-map-Preorder</a> <a id="1063" class="Symbol">:</a>
    <a id="1069" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1074" class="Symbol">(</a><a id="1075" href="order-theory.inflationary-maps-preorders.html#942" class="Bound">l1</a> <a id="1078" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1080" href="order-theory.inflationary-maps-preorders.html#945" class="Bound">l2</a><a id="1082" class="Symbol">)</a>
  <a id="1086" href="order-theory.inflationary-maps-preorders.html#1029" class="Function">is-inflationary-prop-map-Preorder</a> <a id="1120" class="Symbol">=</a>
    <a id="1126" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="1133" class="Symbol">(</a><a id="1134" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="1148" href="order-theory.inflationary-maps-preorders.html#958" class="Bound">P</a><a id="1149" class="Symbol">)</a> <a id="1151" class="Symbol">(λ</a> <a id="1154" href="order-theory.inflationary-maps-preorders.html#1154" class="Bound">x</a> <a id="1156" class="Symbol">→</a> <a id="1158" href="order-theory.preorders.html#1322" class="Function">leq-prop-Preorder</a> <a id="1176" href="order-theory.inflationary-maps-preorders.html#958" class="Bound">P</a> <a id="1178" href="order-theory.inflationary-maps-preorders.html#1154" class="Bound">x</a> <a id="1180" class="Symbol">(</a><a id="1181" href="order-theory.inflationary-maps-preorders.html#979" class="Bound">f</a> <a id="1183" href="order-theory.inflationary-maps-preorders.html#1154" class="Bound">x</a><a id="1184" class="Symbol">))</a>

  <a id="1190" href="order-theory.inflationary-maps-preorders.html#1190" class="Function">is-inflationary-map-Preorder</a> <a id="1219" class="Symbol">:</a>
    <a id="1225" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1228" class="Symbol">(</a><a id="1229" href="order-theory.inflationary-maps-preorders.html#942" class="Bound">l1</a> <a id="1232" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1234" href="order-theory.inflationary-maps-preorders.html#945" class="Bound">l2</a><a id="1236" class="Symbol">)</a>
  <a id="1240" href="order-theory.inflationary-maps-preorders.html#1190" class="Function">is-inflationary-map-Preorder</a> <a id="1269" class="Symbol">=</a>
    <a id="1275" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1285" href="order-theory.inflationary-maps-preorders.html#1029" class="Function">is-inflationary-prop-map-Preorder</a>

  <a id="1322" href="order-theory.inflationary-maps-preorders.html#1322" class="Function">is-prop-is-inflationary-map-Preorder</a> <a id="1359" class="Symbol">:</a>
    <a id="1365" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1373" href="order-theory.inflationary-maps-preorders.html#1190" class="Function">is-inflationary-map-Preorder</a>
  <a id="1404" href="order-theory.inflationary-maps-preorders.html#1322" class="Function">is-prop-is-inflationary-map-Preorder</a> <a id="1441" class="Symbol">=</a>
    <a id="1447" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1465" href="order-theory.inflationary-maps-preorders.html#1029" class="Function">is-inflationary-prop-map-Preorder</a>
</pre>
### The type of inflationary maps on a preorder

<pre class="Agda"><a id="1561" class="Keyword">module</a> <a id="1568" href="order-theory.inflationary-maps-preorders.html#1568" class="Module">_</a>
  <a id="1572" class="Symbol">{</a><a id="1573" href="order-theory.inflationary-maps-preorders.html#1573" class="Bound">l1</a> <a id="1576" href="order-theory.inflationary-maps-preorders.html#1576" class="Bound">l2</a> <a id="1579" class="Symbol">:</a> <a id="1581" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1586" class="Symbol">}</a> <a id="1588" class="Symbol">(</a><a id="1589" href="order-theory.inflationary-maps-preorders.html#1589" class="Bound">P</a> <a id="1591" class="Symbol">:</a> <a id="1593" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="1602" href="order-theory.inflationary-maps-preorders.html#1573" class="Bound">l1</a> <a id="1605" href="order-theory.inflationary-maps-preorders.html#1576" class="Bound">l2</a><a id="1607" class="Symbol">)</a>
  <a id="1611" class="Keyword">where</a>

  <a id="1620" href="order-theory.inflationary-maps-preorders.html#1620" class="Function">inflationary-map-Preorder</a> <a id="1646" class="Symbol">:</a>
    <a id="1652" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1655" class="Symbol">(</a><a id="1656" href="order-theory.inflationary-maps-preorders.html#1573" class="Bound">l1</a> <a id="1659" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1661" href="order-theory.inflationary-maps-preorders.html#1576" class="Bound">l2</a><a id="1663" class="Symbol">)</a>
  <a id="1667" href="order-theory.inflationary-maps-preorders.html#1620" class="Function">inflationary-map-Preorder</a> <a id="1693" class="Symbol">=</a>
    <a id="1699" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="1712" class="Symbol">(</a><a id="1713" href="order-theory.inflationary-maps-preorders.html#1029" class="Function">is-inflationary-prop-map-Preorder</a> <a id="1747" href="order-theory.inflationary-maps-preorders.html#1589" class="Bound">P</a><a id="1748" class="Symbol">)</a>

<a id="1751" class="Keyword">module</a> <a id="1758" href="order-theory.inflationary-maps-preorders.html#1758" class="Module">_</a>
  <a id="1762" class="Symbol">{</a><a id="1763" href="order-theory.inflationary-maps-preorders.html#1763" class="Bound">l1</a> <a id="1766" href="order-theory.inflationary-maps-preorders.html#1766" class="Bound">l2</a> <a id="1769" class="Symbol">:</a> <a id="1771" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1776" class="Symbol">}</a> <a id="1778" class="Symbol">(</a><a id="1779" href="order-theory.inflationary-maps-preorders.html#1779" class="Bound">P</a> <a id="1781" class="Symbol">:</a> <a id="1783" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="1792" href="order-theory.inflationary-maps-preorders.html#1763" class="Bound">l1</a> <a id="1795" href="order-theory.inflationary-maps-preorders.html#1766" class="Bound">l2</a><a id="1797" class="Symbol">)</a> <a id="1799" class="Symbol">(</a><a id="1800" href="order-theory.inflationary-maps-preorders.html#1800" class="Bound">f</a> <a id="1802" class="Symbol">:</a> <a id="1804" href="order-theory.inflationary-maps-preorders.html#1620" class="Function">inflationary-map-Preorder</a> <a id="1830" href="order-theory.inflationary-maps-preorders.html#1779" class="Bound">P</a><a id="1831" class="Symbol">)</a>
  <a id="1835" class="Keyword">where</a>

  <a id="1844" href="order-theory.inflationary-maps-preorders.html#1844" class="Function">map-inflationary-map-Preorder</a> <a id="1874" class="Symbol">:</a>
    <a id="1880" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="1894" href="order-theory.inflationary-maps-preorders.html#1779" class="Bound">P</a> <a id="1896" class="Symbol">→</a> <a id="1898" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="1912" href="order-theory.inflationary-maps-preorders.html#1779" class="Bound">P</a>
  <a id="1916" href="order-theory.inflationary-maps-preorders.html#1844" class="Function">map-inflationary-map-Preorder</a> <a id="1946" class="Symbol">=</a>
    <a id="1952" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1956" href="order-theory.inflationary-maps-preorders.html#1800" class="Bound">f</a>

  <a id="1961" href="order-theory.inflationary-maps-preorders.html#1961" class="Function">is-inflationary-inflationary-map-Preorder</a> <a id="2003" class="Symbol">:</a>
    <a id="2009" href="order-theory.inflationary-maps-preorders.html#1190" class="Function">is-inflationary-map-Preorder</a> <a id="2038" href="order-theory.inflationary-maps-preorders.html#1779" class="Bound">P</a> <a id="2040" href="order-theory.inflationary-maps-preorders.html#1844" class="Function">map-inflationary-map-Preorder</a>
  <a id="2072" href="order-theory.inflationary-maps-preorders.html#1961" class="Function">is-inflationary-inflationary-map-Preorder</a> <a id="2114" class="Symbol">=</a>
    <a id="2120" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2124" href="order-theory.inflationary-maps-preorders.html#1800" class="Bound">f</a>
</pre>
### The predicate on order preserving maps of being inflationary

<pre class="Agda"><a id="2205" class="Keyword">module</a> <a id="2212" href="order-theory.inflationary-maps-preorders.html#2212" class="Module">_</a>
  <a id="2216" class="Symbol">{</a><a id="2217" href="order-theory.inflationary-maps-preorders.html#2217" class="Bound">l1</a> <a id="2220" href="order-theory.inflationary-maps-preorders.html#2220" class="Bound">l2</a> <a id="2223" class="Symbol">:</a> <a id="2225" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2230" class="Symbol">}</a> <a id="2232" class="Symbol">(</a><a id="2233" href="order-theory.inflationary-maps-preorders.html#2233" class="Bound">P</a> <a id="2235" class="Symbol">:</a> <a id="2237" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="2246" href="order-theory.inflationary-maps-preorders.html#2217" class="Bound">l1</a> <a id="2249" href="order-theory.inflationary-maps-preorders.html#2220" class="Bound">l2</a><a id="2251" class="Symbol">)</a> <a id="2253" class="Symbol">(</a><a id="2254" href="order-theory.inflationary-maps-preorders.html#2254" class="Bound">f</a> <a id="2256" class="Symbol">:</a> <a id="2258" href="order-theory.order-preserving-maps-preorders.html#1954" class="Function">hom-Preorder</a> <a id="2271" href="order-theory.inflationary-maps-preorders.html#2233" class="Bound">P</a> <a id="2273" href="order-theory.inflationary-maps-preorders.html#2233" class="Bound">P</a><a id="2274" class="Symbol">)</a>
  <a id="2278" class="Keyword">where</a>

  <a id="2287" href="order-theory.inflationary-maps-preorders.html#2287" class="Function">is-inflationary-prop-hom-Preorder</a> <a id="2321" class="Symbol">:</a> <a id="2323" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2328" class="Symbol">(</a><a id="2329" href="order-theory.inflationary-maps-preorders.html#2217" class="Bound">l1</a> <a id="2332" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2334" href="order-theory.inflationary-maps-preorders.html#2220" class="Bound">l2</a><a id="2336" class="Symbol">)</a>
  <a id="2340" href="order-theory.inflationary-maps-preorders.html#2287" class="Function">is-inflationary-prop-hom-Preorder</a> <a id="2374" class="Symbol">=</a>
    <a id="2380" href="order-theory.inflationary-maps-preorders.html#1029" class="Function">is-inflationary-prop-map-Preorder</a> <a id="2414" href="order-theory.inflationary-maps-preorders.html#2233" class="Bound">P</a> <a id="2416" class="Symbol">(</a><a id="2417" href="order-theory.order-preserving-maps-preorders.html#2089" class="Function">map-hom-Preorder</a> <a id="2434" href="order-theory.inflationary-maps-preorders.html#2233" class="Bound">P</a> <a id="2436" href="order-theory.inflationary-maps-preorders.html#2233" class="Bound">P</a> <a id="2438" href="order-theory.inflationary-maps-preorders.html#2254" class="Bound">f</a><a id="2439" class="Symbol">)</a>

  <a id="2444" href="order-theory.inflationary-maps-preorders.html#2444" class="Function">is-inflationary-hom-Preorder</a> <a id="2473" class="Symbol">:</a> <a id="2475" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2478" class="Symbol">(</a><a id="2479" href="order-theory.inflationary-maps-preorders.html#2217" class="Bound">l1</a> <a id="2482" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2484" href="order-theory.inflationary-maps-preorders.html#2220" class="Bound">l2</a><a id="2486" class="Symbol">)</a>
  <a id="2490" href="order-theory.inflationary-maps-preorders.html#2444" class="Function">is-inflationary-hom-Preorder</a> <a id="2519" class="Symbol">=</a>
    <a id="2525" href="order-theory.inflationary-maps-preorders.html#1190" class="Function">is-inflationary-map-Preorder</a> <a id="2554" href="order-theory.inflationary-maps-preorders.html#2233" class="Bound">P</a> <a id="2556" class="Symbol">(</a><a id="2557" href="order-theory.order-preserving-maps-preorders.html#2089" class="Function">map-hom-Preorder</a> <a id="2574" href="order-theory.inflationary-maps-preorders.html#2233" class="Bound">P</a> <a id="2576" href="order-theory.inflationary-maps-preorders.html#2233" class="Bound">P</a> <a id="2578" href="order-theory.inflationary-maps-preorders.html#2254" class="Bound">f</a><a id="2579" class="Symbol">)</a>

  <a id="2584" href="order-theory.inflationary-maps-preorders.html#2584" class="Function">is-prop-is-inflationary-hom-Preorder</a> <a id="2621" class="Symbol">:</a>
    <a id="2627" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2635" href="order-theory.inflationary-maps-preorders.html#2444" class="Function">is-inflationary-hom-Preorder</a>
  <a id="2666" href="order-theory.inflationary-maps-preorders.html#2584" class="Function">is-prop-is-inflationary-hom-Preorder</a> <a id="2703" class="Symbol">=</a>
    <a id="2709" href="order-theory.inflationary-maps-preorders.html#1322" class="Function">is-prop-is-inflationary-map-Preorder</a> <a id="2746" href="order-theory.inflationary-maps-preorders.html#2233" class="Bound">P</a> <a id="2748" class="Symbol">(</a><a id="2749" href="order-theory.order-preserving-maps-preorders.html#2089" class="Function">map-hom-Preorder</a> <a id="2766" href="order-theory.inflationary-maps-preorders.html#2233" class="Bound">P</a> <a id="2768" href="order-theory.inflationary-maps-preorders.html#2233" class="Bound">P</a> <a id="2770" href="order-theory.inflationary-maps-preorders.html#2254" class="Bound">f</a><a id="2771" class="Symbol">)</a>
</pre>
### The type of inflationary morphisms on a preorder

<pre class="Agda"><a id="2840" class="Keyword">module</a> <a id="2847" href="order-theory.inflationary-maps-preorders.html#2847" class="Module">_</a>
  <a id="2851" class="Symbol">{</a><a id="2852" href="order-theory.inflationary-maps-preorders.html#2852" class="Bound">l1</a> <a id="2855" href="order-theory.inflationary-maps-preorders.html#2855" class="Bound">l2</a> <a id="2858" class="Symbol">:</a> <a id="2860" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2865" class="Symbol">}</a> <a id="2867" class="Symbol">(</a><a id="2868" href="order-theory.inflationary-maps-preorders.html#2868" class="Bound">P</a> <a id="2870" class="Symbol">:</a> <a id="2872" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="2881" href="order-theory.inflationary-maps-preorders.html#2852" class="Bound">l1</a> <a id="2884" href="order-theory.inflationary-maps-preorders.html#2855" class="Bound">l2</a><a id="2886" class="Symbol">)</a>
  <a id="2890" class="Keyword">where</a>

  <a id="2899" href="order-theory.inflationary-maps-preorders.html#2899" class="Function">inflationary-hom-Preorder</a> <a id="2925" class="Symbol">:</a> <a id="2927" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2930" class="Symbol">(</a><a id="2931" href="order-theory.inflationary-maps-preorders.html#2852" class="Bound">l1</a> <a id="2934" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2936" href="order-theory.inflationary-maps-preorders.html#2855" class="Bound">l2</a><a id="2938" class="Symbol">)</a>
  <a id="2942" href="order-theory.inflationary-maps-preorders.html#2899" class="Function">inflationary-hom-Preorder</a> <a id="2968" class="Symbol">=</a>
    <a id="2974" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="2987" class="Symbol">(</a><a id="2988" href="order-theory.inflationary-maps-preorders.html#2287" class="Function">is-inflationary-prop-hom-Preorder</a> <a id="3022" href="order-theory.inflationary-maps-preorders.html#2868" class="Bound">P</a><a id="3023" class="Symbol">)</a>

<a id="3026" class="Keyword">module</a> <a id="3033" href="order-theory.inflationary-maps-preorders.html#3033" class="Module">_</a>
  <a id="3037" class="Symbol">{</a><a id="3038" href="order-theory.inflationary-maps-preorders.html#3038" class="Bound">l1</a> <a id="3041" href="order-theory.inflationary-maps-preorders.html#3041" class="Bound">l2</a> <a id="3044" class="Symbol">:</a> <a id="3046" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3051" class="Symbol">}</a> <a id="3053" class="Symbol">(</a><a id="3054" href="order-theory.inflationary-maps-preorders.html#3054" class="Bound">P</a> <a id="3056" class="Symbol">:</a> <a id="3058" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="3067" href="order-theory.inflationary-maps-preorders.html#3038" class="Bound">l1</a> <a id="3070" href="order-theory.inflationary-maps-preorders.html#3041" class="Bound">l2</a><a id="3072" class="Symbol">)</a> <a id="3074" class="Symbol">(</a><a id="3075" href="order-theory.inflationary-maps-preorders.html#3075" class="Bound">f</a> <a id="3077" class="Symbol">:</a> <a id="3079" href="order-theory.inflationary-maps-preorders.html#2899" class="Function">inflationary-hom-Preorder</a> <a id="3105" href="order-theory.inflationary-maps-preorders.html#3054" class="Bound">P</a><a id="3106" class="Symbol">)</a>
  <a id="3110" class="Keyword">where</a>

  <a id="3119" href="order-theory.inflationary-maps-preorders.html#3119" class="Function">hom-inflationary-hom-Preorder</a> <a id="3149" class="Symbol">:</a>
    <a id="3155" href="order-theory.order-preserving-maps-preorders.html#1954" class="Function">hom-Preorder</a> <a id="3168" href="order-theory.inflationary-maps-preorders.html#3054" class="Bound">P</a> <a id="3170" href="order-theory.inflationary-maps-preorders.html#3054" class="Bound">P</a>
  <a id="3174" href="order-theory.inflationary-maps-preorders.html#3119" class="Function">hom-inflationary-hom-Preorder</a> <a id="3204" class="Symbol">=</a>
    <a id="3210" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3214" href="order-theory.inflationary-maps-preorders.html#3075" class="Bound">f</a>

  <a id="3219" href="order-theory.inflationary-maps-preorders.html#3219" class="Function">map-inflationary-hom-Preorder</a> <a id="3249" class="Symbol">:</a>
    <a id="3255" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="3269" href="order-theory.inflationary-maps-preorders.html#3054" class="Bound">P</a> <a id="3271" class="Symbol">→</a> <a id="3273" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="3287" href="order-theory.inflationary-maps-preorders.html#3054" class="Bound">P</a>
  <a id="3291" href="order-theory.inflationary-maps-preorders.html#3219" class="Function">map-inflationary-hom-Preorder</a> <a id="3321" class="Symbol">=</a>
    <a id="3327" href="order-theory.order-preserving-maps-preorders.html#2089" class="Function">map-hom-Preorder</a> <a id="3344" href="order-theory.inflationary-maps-preorders.html#3054" class="Bound">P</a> <a id="3346" href="order-theory.inflationary-maps-preorders.html#3054" class="Bound">P</a> <a id="3348" href="order-theory.inflationary-maps-preorders.html#3119" class="Function">hom-inflationary-hom-Preorder</a>

  <a id="3381" href="order-theory.inflationary-maps-preorders.html#3381" class="Function">preserves-order-inflationary-hom-Preorder</a> <a id="3423" class="Symbol">:</a>
    <a id="3429" href="order-theory.order-preserving-maps-preorders.html#1530" class="Function">preserves-order-Preorder</a> <a id="3454" href="order-theory.inflationary-maps-preorders.html#3054" class="Bound">P</a> <a id="3456" href="order-theory.inflationary-maps-preorders.html#3054" class="Bound">P</a> <a id="3458" href="order-theory.inflationary-maps-preorders.html#3219" class="Function">map-inflationary-hom-Preorder</a>
  <a id="3490" href="order-theory.inflationary-maps-preorders.html#3381" class="Function">preserves-order-inflationary-hom-Preorder</a> <a id="3532" class="Symbol">=</a>
    <a id="3538" href="order-theory.order-preserving-maps-preorders.html#2193" class="Function">preserves-order-hom-Preorder</a> <a id="3567" href="order-theory.inflationary-maps-preorders.html#3054" class="Bound">P</a> <a id="3569" href="order-theory.inflationary-maps-preorders.html#3054" class="Bound">P</a> <a id="3571" href="order-theory.inflationary-maps-preorders.html#3119" class="Function">hom-inflationary-hom-Preorder</a>

  <a id="3604" href="order-theory.inflationary-maps-preorders.html#3604" class="Function">is-inflationary-inflationary-hom-Preorder</a> <a id="3646" class="Symbol">:</a>
    <a id="3652" href="order-theory.inflationary-maps-preorders.html#1190" class="Function">is-inflationary-map-Preorder</a> <a id="3681" href="order-theory.inflationary-maps-preorders.html#3054" class="Bound">P</a> <a id="3683" href="order-theory.inflationary-maps-preorders.html#3219" class="Function">map-inflationary-hom-Preorder</a>
  <a id="3715" href="order-theory.inflationary-maps-preorders.html#3604" class="Function">is-inflationary-inflationary-hom-Preorder</a> <a id="3757" class="Symbol">=</a>
    <a id="3763" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3767" href="order-theory.inflationary-maps-preorders.html#3075" class="Bound">f</a>

  <a id="3772" href="order-theory.inflationary-maps-preorders.html#3772" class="Function">inflationary-map-inflationary-hom-Preorder</a> <a id="3815" class="Symbol">:</a>
    <a id="3821" href="order-theory.inflationary-maps-preorders.html#1620" class="Function">inflationary-map-Preorder</a> <a id="3847" href="order-theory.inflationary-maps-preorders.html#3054" class="Bound">P</a>
  <a id="3851" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3855" href="order-theory.inflationary-maps-preorders.html#3772" class="Function">inflationary-map-inflationary-hom-Preorder</a> <a id="3898" class="Symbol">=</a>
    <a id="3904" href="order-theory.inflationary-maps-preorders.html#3219" class="Function">map-inflationary-hom-Preorder</a>
  <a id="3936" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3940" href="order-theory.inflationary-maps-preorders.html#3772" class="Function">inflationary-map-inflationary-hom-Preorder</a> <a id="3983" class="Symbol">=</a>
    <a id="3989" href="order-theory.inflationary-maps-preorders.html#3604" class="Function">is-inflationary-inflationary-hom-Preorder</a>
</pre>