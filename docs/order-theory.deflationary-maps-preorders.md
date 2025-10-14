# Deflationary maps on a preorder

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="order-theory.deflationary-maps-preorders.html" class="Module">order-theory.deflationary-maps-preorders</a> <a id="92" class="Keyword">where</a>
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

A map $f : P → P$ on a [preorder](order-theory.preorders.md) $P$ is said to be a
{{#concept "deflationary map" Disambiguation="preorder" Agda=deflationary-map-Preorder}}
if the inequality

$$
  f(x) ≤ x
$$

holds for any element $x : P$. If $f$ is also
[order preserving](order-theory.order-preserving-maps-preorders.md) we say that
$f$ is a
{{#concept "deflationary morphism" Disambiguation="preorder" Agda=deflationary-hom-Preorder}}.

## Definitions

### The predicate of being a deflationary map

<pre class="Agda"><a id="927" class="Keyword">module</a> <a id="934" href="order-theory.deflationary-maps-preorders.html#934" class="Module">_</a>
  <a id="938" class="Symbol">{</a><a id="939" href="order-theory.deflationary-maps-preorders.html#939" class="Bound">l1</a> <a id="942" href="order-theory.deflationary-maps-preorders.html#942" class="Bound">l2</a> <a id="945" class="Symbol">:</a> <a id="947" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="952" class="Symbol">}</a> <a id="954" class="Symbol">(</a><a id="955" href="order-theory.deflationary-maps-preorders.html#955" class="Bound">P</a> <a id="957" class="Symbol">:</a> <a id="959" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="968" href="order-theory.deflationary-maps-preorders.html#939" class="Bound">l1</a> <a id="971" href="order-theory.deflationary-maps-preorders.html#942" class="Bound">l2</a><a id="973" class="Symbol">)</a> <a id="975" class="Symbol">(</a><a id="976" href="order-theory.deflationary-maps-preorders.html#976" class="Bound">f</a> <a id="978" class="Symbol">:</a> <a id="980" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="994" href="order-theory.deflationary-maps-preorders.html#955" class="Bound">P</a> <a id="996" class="Symbol">→</a> <a id="998" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="1012" href="order-theory.deflationary-maps-preorders.html#955" class="Bound">P</a><a id="1013" class="Symbol">)</a>
  <a id="1017" class="Keyword">where</a>

  <a id="1026" href="order-theory.deflationary-maps-preorders.html#1026" class="Function">is-deflationary-prop-map-Preorder</a> <a id="1060" class="Symbol">:</a>
    <a id="1066" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1071" class="Symbol">(</a><a id="1072" href="order-theory.deflationary-maps-preorders.html#939" class="Bound">l1</a> <a id="1075" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1077" href="order-theory.deflationary-maps-preorders.html#942" class="Bound">l2</a><a id="1079" class="Symbol">)</a>
  <a id="1083" href="order-theory.deflationary-maps-preorders.html#1026" class="Function">is-deflationary-prop-map-Preorder</a> <a id="1117" class="Symbol">=</a>
    <a id="1123" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="1130" class="Symbol">(</a><a id="1131" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="1145" href="order-theory.deflationary-maps-preorders.html#955" class="Bound">P</a><a id="1146" class="Symbol">)</a> <a id="1148" class="Symbol">(λ</a> <a id="1151" href="order-theory.deflationary-maps-preorders.html#1151" class="Bound">x</a> <a id="1153" class="Symbol">→</a> <a id="1155" href="order-theory.preorders.html#1322" class="Function">leq-prop-Preorder</a> <a id="1173" href="order-theory.deflationary-maps-preorders.html#955" class="Bound">P</a> <a id="1175" class="Symbol">(</a><a id="1176" href="order-theory.deflationary-maps-preorders.html#976" class="Bound">f</a> <a id="1178" href="order-theory.deflationary-maps-preorders.html#1151" class="Bound">x</a><a id="1179" class="Symbol">)</a> <a id="1181" href="order-theory.deflationary-maps-preorders.html#1151" class="Bound">x</a><a id="1182" class="Symbol">)</a>

  <a id="1187" href="order-theory.deflationary-maps-preorders.html#1187" class="Function">is-deflationary-map-Preorder</a> <a id="1216" class="Symbol">:</a>
    <a id="1222" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1225" class="Symbol">(</a><a id="1226" href="order-theory.deflationary-maps-preorders.html#939" class="Bound">l1</a> <a id="1229" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1231" href="order-theory.deflationary-maps-preorders.html#942" class="Bound">l2</a><a id="1233" class="Symbol">)</a>
  <a id="1237" href="order-theory.deflationary-maps-preorders.html#1187" class="Function">is-deflationary-map-Preorder</a> <a id="1266" class="Symbol">=</a>
    <a id="1272" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1282" href="order-theory.deflationary-maps-preorders.html#1026" class="Function">is-deflationary-prop-map-Preorder</a>

  <a id="1319" href="order-theory.deflationary-maps-preorders.html#1319" class="Function">is-prop-is-deflationary-map-Preorder</a> <a id="1356" class="Symbol">:</a>
    <a id="1362" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1370" href="order-theory.deflationary-maps-preorders.html#1187" class="Function">is-deflationary-map-Preorder</a>
  <a id="1401" href="order-theory.deflationary-maps-preorders.html#1319" class="Function">is-prop-is-deflationary-map-Preorder</a> <a id="1438" class="Symbol">=</a>
    <a id="1444" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1462" href="order-theory.deflationary-maps-preorders.html#1026" class="Function">is-deflationary-prop-map-Preorder</a>
</pre>
### The type of deflationary maps on a preorder

<pre class="Agda"><a id="1558" class="Keyword">module</a> <a id="1565" href="order-theory.deflationary-maps-preorders.html#1565" class="Module">_</a>
  <a id="1569" class="Symbol">{</a><a id="1570" href="order-theory.deflationary-maps-preorders.html#1570" class="Bound">l1</a> <a id="1573" href="order-theory.deflationary-maps-preorders.html#1573" class="Bound">l2</a> <a id="1576" class="Symbol">:</a> <a id="1578" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1583" class="Symbol">}</a> <a id="1585" class="Symbol">(</a><a id="1586" href="order-theory.deflationary-maps-preorders.html#1586" class="Bound">P</a> <a id="1588" class="Symbol">:</a> <a id="1590" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="1599" href="order-theory.deflationary-maps-preorders.html#1570" class="Bound">l1</a> <a id="1602" href="order-theory.deflationary-maps-preorders.html#1573" class="Bound">l2</a><a id="1604" class="Symbol">)</a>
  <a id="1608" class="Keyword">where</a>

  <a id="1617" href="order-theory.deflationary-maps-preorders.html#1617" class="Function">deflationary-map-Preorder</a> <a id="1643" class="Symbol">:</a>
    <a id="1649" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1652" class="Symbol">(</a><a id="1653" href="order-theory.deflationary-maps-preorders.html#1570" class="Bound">l1</a> <a id="1656" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1658" href="order-theory.deflationary-maps-preorders.html#1573" class="Bound">l2</a><a id="1660" class="Symbol">)</a>
  <a id="1664" href="order-theory.deflationary-maps-preorders.html#1617" class="Function">deflationary-map-Preorder</a> <a id="1690" class="Symbol">=</a>
    <a id="1696" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="1709" class="Symbol">(</a><a id="1710" href="order-theory.deflationary-maps-preorders.html#1026" class="Function">is-deflationary-prop-map-Preorder</a> <a id="1744" href="order-theory.deflationary-maps-preorders.html#1586" class="Bound">P</a><a id="1745" class="Symbol">)</a>

<a id="1748" class="Keyword">module</a> <a id="1755" href="order-theory.deflationary-maps-preorders.html#1755" class="Module">_</a>
  <a id="1759" class="Symbol">{</a><a id="1760" href="order-theory.deflationary-maps-preorders.html#1760" class="Bound">l1</a> <a id="1763" href="order-theory.deflationary-maps-preorders.html#1763" class="Bound">l2</a> <a id="1766" class="Symbol">:</a> <a id="1768" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1773" class="Symbol">}</a> <a id="1775" class="Symbol">(</a><a id="1776" href="order-theory.deflationary-maps-preorders.html#1776" class="Bound">P</a> <a id="1778" class="Symbol">:</a> <a id="1780" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="1789" href="order-theory.deflationary-maps-preorders.html#1760" class="Bound">l1</a> <a id="1792" href="order-theory.deflationary-maps-preorders.html#1763" class="Bound">l2</a><a id="1794" class="Symbol">)</a> <a id="1796" class="Symbol">(</a><a id="1797" href="order-theory.deflationary-maps-preorders.html#1797" class="Bound">f</a> <a id="1799" class="Symbol">:</a> <a id="1801" href="order-theory.deflationary-maps-preorders.html#1617" class="Function">deflationary-map-Preorder</a> <a id="1827" href="order-theory.deflationary-maps-preorders.html#1776" class="Bound">P</a><a id="1828" class="Symbol">)</a>
  <a id="1832" class="Keyword">where</a>

  <a id="1841" href="order-theory.deflationary-maps-preorders.html#1841" class="Function">map-deflationary-map-Preorder</a> <a id="1871" class="Symbol">:</a>
    <a id="1877" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="1891" href="order-theory.deflationary-maps-preorders.html#1776" class="Bound">P</a> <a id="1893" class="Symbol">→</a> <a id="1895" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="1909" href="order-theory.deflationary-maps-preorders.html#1776" class="Bound">P</a>
  <a id="1913" href="order-theory.deflationary-maps-preorders.html#1841" class="Function">map-deflationary-map-Preorder</a> <a id="1943" class="Symbol">=</a>
    <a id="1949" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1953" href="order-theory.deflationary-maps-preorders.html#1797" class="Bound">f</a>

  <a id="1958" href="order-theory.deflationary-maps-preorders.html#1958" class="Function">is-deflationary-deflationary-map-Preorder</a> <a id="2000" class="Symbol">:</a>
    <a id="2006" href="order-theory.deflationary-maps-preorders.html#1187" class="Function">is-deflationary-map-Preorder</a> <a id="2035" href="order-theory.deflationary-maps-preorders.html#1776" class="Bound">P</a> <a id="2037" href="order-theory.deflationary-maps-preorders.html#1841" class="Function">map-deflationary-map-Preorder</a>
  <a id="2069" href="order-theory.deflationary-maps-preorders.html#1958" class="Function">is-deflationary-deflationary-map-Preorder</a> <a id="2111" class="Symbol">=</a>
    <a id="2117" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2121" href="order-theory.deflationary-maps-preorders.html#1797" class="Bound">f</a>
</pre>
### The predicate on order preserving maps of being deflationary

<pre class="Agda"><a id="2202" class="Keyword">module</a> <a id="2209" href="order-theory.deflationary-maps-preorders.html#2209" class="Module">_</a>
  <a id="2213" class="Symbol">{</a><a id="2214" href="order-theory.deflationary-maps-preorders.html#2214" class="Bound">l1</a> <a id="2217" href="order-theory.deflationary-maps-preorders.html#2217" class="Bound">l2</a> <a id="2220" class="Symbol">:</a> <a id="2222" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2227" class="Symbol">}</a> <a id="2229" class="Symbol">(</a><a id="2230" href="order-theory.deflationary-maps-preorders.html#2230" class="Bound">P</a> <a id="2232" class="Symbol">:</a> <a id="2234" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="2243" href="order-theory.deflationary-maps-preorders.html#2214" class="Bound">l1</a> <a id="2246" href="order-theory.deflationary-maps-preorders.html#2217" class="Bound">l2</a><a id="2248" class="Symbol">)</a> <a id="2250" class="Symbol">(</a><a id="2251" href="order-theory.deflationary-maps-preorders.html#2251" class="Bound">f</a> <a id="2253" class="Symbol">:</a> <a id="2255" href="order-theory.order-preserving-maps-preorders.html#1954" class="Function">hom-Preorder</a> <a id="2268" href="order-theory.deflationary-maps-preorders.html#2230" class="Bound">P</a> <a id="2270" href="order-theory.deflationary-maps-preorders.html#2230" class="Bound">P</a><a id="2271" class="Symbol">)</a>
  <a id="2275" class="Keyword">where</a>

  <a id="2284" href="order-theory.deflationary-maps-preorders.html#2284" class="Function">is-deflationary-prop-hom-Preorder</a> <a id="2318" class="Symbol">:</a> <a id="2320" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2325" class="Symbol">(</a><a id="2326" href="order-theory.deflationary-maps-preorders.html#2214" class="Bound">l1</a> <a id="2329" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2331" href="order-theory.deflationary-maps-preorders.html#2217" class="Bound">l2</a><a id="2333" class="Symbol">)</a>
  <a id="2337" href="order-theory.deflationary-maps-preorders.html#2284" class="Function">is-deflationary-prop-hom-Preorder</a> <a id="2371" class="Symbol">=</a>
    <a id="2377" href="order-theory.deflationary-maps-preorders.html#1026" class="Function">is-deflationary-prop-map-Preorder</a> <a id="2411" href="order-theory.deflationary-maps-preorders.html#2230" class="Bound">P</a> <a id="2413" class="Symbol">(</a><a id="2414" href="order-theory.order-preserving-maps-preorders.html#2089" class="Function">map-hom-Preorder</a> <a id="2431" href="order-theory.deflationary-maps-preorders.html#2230" class="Bound">P</a> <a id="2433" href="order-theory.deflationary-maps-preorders.html#2230" class="Bound">P</a> <a id="2435" href="order-theory.deflationary-maps-preorders.html#2251" class="Bound">f</a><a id="2436" class="Symbol">)</a>

  <a id="2441" href="order-theory.deflationary-maps-preorders.html#2441" class="Function">is-deflationary-hom-Preorder</a> <a id="2470" class="Symbol">:</a> <a id="2472" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2475" class="Symbol">(</a><a id="2476" href="order-theory.deflationary-maps-preorders.html#2214" class="Bound">l1</a> <a id="2479" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2481" href="order-theory.deflationary-maps-preorders.html#2217" class="Bound">l2</a><a id="2483" class="Symbol">)</a>
  <a id="2487" href="order-theory.deflationary-maps-preorders.html#2441" class="Function">is-deflationary-hom-Preorder</a> <a id="2516" class="Symbol">=</a>
    <a id="2522" href="order-theory.deflationary-maps-preorders.html#1187" class="Function">is-deflationary-map-Preorder</a> <a id="2551" href="order-theory.deflationary-maps-preorders.html#2230" class="Bound">P</a> <a id="2553" class="Symbol">(</a><a id="2554" href="order-theory.order-preserving-maps-preorders.html#2089" class="Function">map-hom-Preorder</a> <a id="2571" href="order-theory.deflationary-maps-preorders.html#2230" class="Bound">P</a> <a id="2573" href="order-theory.deflationary-maps-preorders.html#2230" class="Bound">P</a> <a id="2575" href="order-theory.deflationary-maps-preorders.html#2251" class="Bound">f</a><a id="2576" class="Symbol">)</a>

  <a id="2581" href="order-theory.deflationary-maps-preorders.html#2581" class="Function">is-prop-is-deflationary-hom-Preorder</a> <a id="2618" class="Symbol">:</a>
    <a id="2624" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2632" href="order-theory.deflationary-maps-preorders.html#2441" class="Function">is-deflationary-hom-Preorder</a>
  <a id="2663" href="order-theory.deflationary-maps-preorders.html#2581" class="Function">is-prop-is-deflationary-hom-Preorder</a> <a id="2700" class="Symbol">=</a>
    <a id="2706" href="order-theory.deflationary-maps-preorders.html#1319" class="Function">is-prop-is-deflationary-map-Preorder</a> <a id="2743" href="order-theory.deflationary-maps-preorders.html#2230" class="Bound">P</a> <a id="2745" class="Symbol">(</a><a id="2746" href="order-theory.order-preserving-maps-preorders.html#2089" class="Function">map-hom-Preorder</a> <a id="2763" href="order-theory.deflationary-maps-preorders.html#2230" class="Bound">P</a> <a id="2765" href="order-theory.deflationary-maps-preorders.html#2230" class="Bound">P</a> <a id="2767" href="order-theory.deflationary-maps-preorders.html#2251" class="Bound">f</a><a id="2768" class="Symbol">)</a>
</pre>
### The type of deflationary morphisms on a preorder

<pre class="Agda"><a id="2837" class="Keyword">module</a> <a id="2844" href="order-theory.deflationary-maps-preorders.html#2844" class="Module">_</a>
  <a id="2848" class="Symbol">{</a><a id="2849" href="order-theory.deflationary-maps-preorders.html#2849" class="Bound">l1</a> <a id="2852" href="order-theory.deflationary-maps-preorders.html#2852" class="Bound">l2</a> <a id="2855" class="Symbol">:</a> <a id="2857" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2862" class="Symbol">}</a> <a id="2864" class="Symbol">(</a><a id="2865" href="order-theory.deflationary-maps-preorders.html#2865" class="Bound">P</a> <a id="2867" class="Symbol">:</a> <a id="2869" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="2878" href="order-theory.deflationary-maps-preorders.html#2849" class="Bound">l1</a> <a id="2881" href="order-theory.deflationary-maps-preorders.html#2852" class="Bound">l2</a><a id="2883" class="Symbol">)</a>
  <a id="2887" class="Keyword">where</a>

  <a id="2896" href="order-theory.deflationary-maps-preorders.html#2896" class="Function">deflationary-hom-Preorder</a> <a id="2922" class="Symbol">:</a> <a id="2924" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2927" class="Symbol">(</a><a id="2928" href="order-theory.deflationary-maps-preorders.html#2849" class="Bound">l1</a> <a id="2931" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2933" href="order-theory.deflationary-maps-preorders.html#2852" class="Bound">l2</a><a id="2935" class="Symbol">)</a>
  <a id="2939" href="order-theory.deflationary-maps-preorders.html#2896" class="Function">deflationary-hom-Preorder</a> <a id="2965" class="Symbol">=</a>
    <a id="2971" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="2984" class="Symbol">(</a><a id="2985" href="order-theory.deflationary-maps-preorders.html#2284" class="Function">is-deflationary-prop-hom-Preorder</a> <a id="3019" href="order-theory.deflationary-maps-preorders.html#2865" class="Bound">P</a><a id="3020" class="Symbol">)</a>

<a id="3023" class="Keyword">module</a> <a id="3030" href="order-theory.deflationary-maps-preorders.html#3030" class="Module">_</a>
  <a id="3034" class="Symbol">{</a><a id="3035" href="order-theory.deflationary-maps-preorders.html#3035" class="Bound">l1</a> <a id="3038" href="order-theory.deflationary-maps-preorders.html#3038" class="Bound">l2</a> <a id="3041" class="Symbol">:</a> <a id="3043" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3048" class="Symbol">}</a> <a id="3050" class="Symbol">(</a><a id="3051" href="order-theory.deflationary-maps-preorders.html#3051" class="Bound">P</a> <a id="3053" class="Symbol">:</a> <a id="3055" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="3064" href="order-theory.deflationary-maps-preorders.html#3035" class="Bound">l1</a> <a id="3067" href="order-theory.deflationary-maps-preorders.html#3038" class="Bound">l2</a><a id="3069" class="Symbol">)</a> <a id="3071" class="Symbol">(</a><a id="3072" href="order-theory.deflationary-maps-preorders.html#3072" class="Bound">f</a> <a id="3074" class="Symbol">:</a> <a id="3076" href="order-theory.deflationary-maps-preorders.html#2896" class="Function">deflationary-hom-Preorder</a> <a id="3102" href="order-theory.deflationary-maps-preorders.html#3051" class="Bound">P</a><a id="3103" class="Symbol">)</a>
  <a id="3107" class="Keyword">where</a>

  <a id="3116" href="order-theory.deflationary-maps-preorders.html#3116" class="Function">hom-deflationary-hom-Preorder</a> <a id="3146" class="Symbol">:</a>
    <a id="3152" href="order-theory.order-preserving-maps-preorders.html#1954" class="Function">hom-Preorder</a> <a id="3165" href="order-theory.deflationary-maps-preorders.html#3051" class="Bound">P</a> <a id="3167" href="order-theory.deflationary-maps-preorders.html#3051" class="Bound">P</a>
  <a id="3171" href="order-theory.deflationary-maps-preorders.html#3116" class="Function">hom-deflationary-hom-Preorder</a> <a id="3201" class="Symbol">=</a>
    <a id="3207" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3211" href="order-theory.deflationary-maps-preorders.html#3072" class="Bound">f</a>

  <a id="3216" href="order-theory.deflationary-maps-preorders.html#3216" class="Function">map-deflationary-hom-Preorder</a> <a id="3246" class="Symbol">:</a>
    <a id="3252" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="3266" href="order-theory.deflationary-maps-preorders.html#3051" class="Bound">P</a> <a id="3268" class="Symbol">→</a> <a id="3270" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="3284" href="order-theory.deflationary-maps-preorders.html#3051" class="Bound">P</a>
  <a id="3288" href="order-theory.deflationary-maps-preorders.html#3216" class="Function">map-deflationary-hom-Preorder</a> <a id="3318" class="Symbol">=</a>
    <a id="3324" href="order-theory.order-preserving-maps-preorders.html#2089" class="Function">map-hom-Preorder</a> <a id="3341" href="order-theory.deflationary-maps-preorders.html#3051" class="Bound">P</a> <a id="3343" href="order-theory.deflationary-maps-preorders.html#3051" class="Bound">P</a> <a id="3345" href="order-theory.deflationary-maps-preorders.html#3116" class="Function">hom-deflationary-hom-Preorder</a>

  <a id="3378" href="order-theory.deflationary-maps-preorders.html#3378" class="Function">preserves-order-deflationary-hom-Preorder</a> <a id="3420" class="Symbol">:</a>
    <a id="3426" href="order-theory.order-preserving-maps-preorders.html#1530" class="Function">preserves-order-Preorder</a> <a id="3451" href="order-theory.deflationary-maps-preorders.html#3051" class="Bound">P</a> <a id="3453" href="order-theory.deflationary-maps-preorders.html#3051" class="Bound">P</a> <a id="3455" href="order-theory.deflationary-maps-preorders.html#3216" class="Function">map-deflationary-hom-Preorder</a>
  <a id="3487" href="order-theory.deflationary-maps-preorders.html#3378" class="Function">preserves-order-deflationary-hom-Preorder</a> <a id="3529" class="Symbol">=</a>
    <a id="3535" href="order-theory.order-preserving-maps-preorders.html#2193" class="Function">preserves-order-hom-Preorder</a> <a id="3564" href="order-theory.deflationary-maps-preorders.html#3051" class="Bound">P</a> <a id="3566" href="order-theory.deflationary-maps-preorders.html#3051" class="Bound">P</a> <a id="3568" href="order-theory.deflationary-maps-preorders.html#3116" class="Function">hom-deflationary-hom-Preorder</a>

  <a id="3601" href="order-theory.deflationary-maps-preorders.html#3601" class="Function">is-deflationary-deflationary-hom-Preorder</a> <a id="3643" class="Symbol">:</a>
    <a id="3649" href="order-theory.deflationary-maps-preorders.html#1187" class="Function">is-deflationary-map-Preorder</a> <a id="3678" href="order-theory.deflationary-maps-preorders.html#3051" class="Bound">P</a> <a id="3680" href="order-theory.deflationary-maps-preorders.html#3216" class="Function">map-deflationary-hom-Preorder</a>
  <a id="3712" href="order-theory.deflationary-maps-preorders.html#3601" class="Function">is-deflationary-deflationary-hom-Preorder</a> <a id="3754" class="Symbol">=</a>
    <a id="3760" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3764" href="order-theory.deflationary-maps-preorders.html#3072" class="Bound">f</a>

  <a id="3769" href="order-theory.deflationary-maps-preorders.html#3769" class="Function">deflationary-map-deflationary-hom-Preorder</a> <a id="3812" class="Symbol">:</a>
    <a id="3818" href="order-theory.deflationary-maps-preorders.html#1617" class="Function">deflationary-map-Preorder</a> <a id="3844" href="order-theory.deflationary-maps-preorders.html#3051" class="Bound">P</a>
  <a id="3848" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3852" href="order-theory.deflationary-maps-preorders.html#3769" class="Function">deflationary-map-deflationary-hom-Preorder</a> <a id="3895" class="Symbol">=</a>
    <a id="3901" href="order-theory.deflationary-maps-preorders.html#3216" class="Function">map-deflationary-hom-Preorder</a>
  <a id="3933" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3937" href="order-theory.deflationary-maps-preorders.html#3769" class="Function">deflationary-map-deflationary-hom-Preorder</a> <a id="3980" class="Symbol">=</a>
    <a id="3986" href="order-theory.deflationary-maps-preorders.html#3601" class="Function">is-deflationary-deflationary-hom-Preorder</a>
</pre>