# Strictly inflationary maps on a strictly preordered type

<pre class="Agda"><a id="69" class="Keyword">module</a> <a id="76" href="order-theory.strictly-inflationary-maps-strict-preorders.html" class="Module">order-theory.strictly-inflationary-maps-strict-preorders</a> <a id="133" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="233" class="Keyword">open</a> <a id="238" class="Keyword">import</a> <a id="245" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="269" class="Keyword">open</a> <a id="274" class="Keyword">import</a> <a id="281" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="301" class="Keyword">open</a> <a id="306" class="Keyword">import</a> <a id="313" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="341" class="Keyword">open</a> <a id="346" class="Keyword">import</a> <a id="353" href="order-theory.strict-order-preserving-maps.html" class="Module">order-theory.strict-order-preserving-maps</a>
<a id="395" class="Keyword">open</a> <a id="400" class="Keyword">import</a> <a id="407" href="order-theory.strict-preorders.html" class="Module">order-theory.strict-preorders</a>
</pre>
</details>

## Idea

A map $f : P → P$ on a [strict preorder](order-theory.strict-preorders.md) $P$
is said to be a
{{#concept "strictly inflationary map" Disambiguation="strict preorder" Agda=strictly-inflationary-map-Strict-Preorder}}
if the inequality

$$
  x < f(x)
$$

holds for any element $x : P$. If $f$ is also
[order preserving](order-theory.strict-order-preserving-maps.md) we say that $f$
is a
{{#concept "strictly inflationary morphism" Disambiguation="strict preorder" Agda=inflationary-hom-Strict-Preorder}}.

## Definitions

### The predicate of being a strictly inflationary map

<pre class="Agda"><a id="1047" class="Keyword">module</a> <a id="1054" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1054" class="Module">_</a>
  <a id="1058" class="Symbol">{</a><a id="1059" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1059" class="Bound">l1</a> <a id="1062" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1062" class="Bound">l2</a> <a id="1065" class="Symbol">:</a> <a id="1067" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1072" class="Symbol">}</a> <a id="1074" class="Symbol">(</a><a id="1075" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1075" class="Bound">P</a> <a id="1077" class="Symbol">:</a> <a id="1079" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="1095" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1059" class="Bound">l1</a> <a id="1098" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1062" class="Bound">l2</a><a id="1100" class="Symbol">)</a>
  <a id="1104" class="Symbol">(</a><a id="1105" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1105" class="Bound">f</a> <a id="1107" class="Symbol">:</a> <a id="1109" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a> <a id="1130" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1075" class="Bound">P</a> <a id="1132" class="Symbol">→</a> <a id="1134" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a> <a id="1155" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1075" class="Bound">P</a><a id="1156" class="Symbol">)</a>
  <a id="1160" class="Keyword">where</a>

  <a id="1169" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1169" class="Function">is-strictly-inflationary-map-prop-Strict-Preorder</a> <a id="1219" class="Symbol">:</a>
    <a id="1225" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1230" class="Symbol">(</a><a id="1231" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1059" class="Bound">l1</a> <a id="1234" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1236" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1062" class="Bound">l2</a><a id="1238" class="Symbol">)</a>
  <a id="1242" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1169" class="Function">is-strictly-inflationary-map-prop-Strict-Preorder</a> <a id="1292" class="Symbol">=</a>
    <a id="1298" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="1311" class="Symbol">(</a> <a id="1313" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a> <a id="1334" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1075" class="Bound">P</a><a id="1335" class="Symbol">)</a>
      <a id="1343" class="Symbol">(</a> <a id="1345" class="Symbol">λ</a> <a id="1347" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1347" class="Bound">x</a> <a id="1349" class="Symbol">→</a> <a id="1351" href="order-theory.strict-preorders.html#1459" class="Function">le-prop-Strict-Preorder</a> <a id="1375" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1075" class="Bound">P</a> <a id="1377" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1347" class="Bound">x</a> <a id="1379" class="Symbol">(</a><a id="1380" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1105" class="Bound">f</a> <a id="1382" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1347" class="Bound">x</a><a id="1383" class="Symbol">))</a>

  <a id="1389" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1389" class="Function">is-strictly-inflationary-map-Strict-Preorder</a> <a id="1434" class="Symbol">:</a>
    <a id="1440" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1443" class="Symbol">(</a><a id="1444" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1059" class="Bound">l1</a> <a id="1447" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1449" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1062" class="Bound">l2</a><a id="1451" class="Symbol">)</a>
  <a id="1455" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1389" class="Function">is-strictly-inflationary-map-Strict-Preorder</a> <a id="1500" class="Symbol">=</a>
    <a id="1506" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1516" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1169" class="Function">is-strictly-inflationary-map-prop-Strict-Preorder</a>

  <a id="1569" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1569" class="Function">is-prop-is-strictly-inflationary-map-Strict-Preorder</a> <a id="1622" class="Symbol">:</a>
    <a id="1628" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1636" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1389" class="Function">is-strictly-inflationary-map-Strict-Preorder</a>
  <a id="1683" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1569" class="Function">is-prop-is-strictly-inflationary-map-Strict-Preorder</a> <a id="1736" class="Symbol">=</a>
    <a id="1742" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1760" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1169" class="Function">is-strictly-inflationary-map-prop-Strict-Preorder</a>
</pre>
### The type of inflationary maps on a strict preorder

<pre class="Agda"><a id="1879" class="Keyword">module</a> <a id="1886" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1886" class="Module">_</a>
  <a id="1890" class="Symbol">{</a><a id="1891" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1891" class="Bound">l1</a> <a id="1894" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1894" class="Bound">l2</a> <a id="1897" class="Symbol">:</a> <a id="1899" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1904" class="Symbol">}</a> <a id="1906" class="Symbol">(</a><a id="1907" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1907" class="Bound">P</a> <a id="1909" class="Symbol">:</a> <a id="1911" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="1927" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1891" class="Bound">l1</a> <a id="1930" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1894" class="Bound">l2</a><a id="1932" class="Symbol">)</a>
  <a id="1936" class="Keyword">where</a>

  <a id="1945" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1945" class="Function">strictly-inflationary-map-Strict-Preorder</a> <a id="1987" class="Symbol">:</a>
    <a id="1993" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1996" class="Symbol">(</a><a id="1997" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1891" class="Bound">l1</a> <a id="2000" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2002" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1894" class="Bound">l2</a><a id="2004" class="Symbol">)</a>
  <a id="2008" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1945" class="Function">strictly-inflationary-map-Strict-Preorder</a> <a id="2050" class="Symbol">=</a>
    <a id="2056" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="2069" class="Symbol">(</a><a id="2070" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1169" class="Function">is-strictly-inflationary-map-prop-Strict-Preorder</a> <a id="2120" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1907" class="Bound">P</a><a id="2121" class="Symbol">)</a>

<a id="2124" class="Keyword">module</a> <a id="2131" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2131" class="Module">_</a>
  <a id="2135" class="Symbol">{</a><a id="2136" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2136" class="Bound">l1</a> <a id="2139" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2139" class="Bound">l2</a> <a id="2142" class="Symbol">:</a> <a id="2144" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2149" class="Symbol">}</a> <a id="2151" class="Symbol">(</a><a id="2152" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2152" class="Bound">P</a> <a id="2154" class="Symbol">:</a> <a id="2156" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="2172" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2136" class="Bound">l1</a> <a id="2175" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2139" class="Bound">l2</a><a id="2177" class="Symbol">)</a>
  <a id="2181" class="Symbol">(</a><a id="2182" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2182" class="Bound">f</a> <a id="2184" class="Symbol">:</a> <a id="2186" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1945" class="Function">strictly-inflationary-map-Strict-Preorder</a> <a id="2228" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2152" class="Bound">P</a><a id="2229" class="Symbol">)</a>
  <a id="2233" class="Keyword">where</a>

  <a id="2242" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2242" class="Function">map-strictly-inflationary-map-Strict-Preorder</a> <a id="2288" class="Symbol">:</a>
    <a id="2294" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a> <a id="2315" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2152" class="Bound">P</a> <a id="2317" class="Symbol">→</a> <a id="2319" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a> <a id="2340" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2152" class="Bound">P</a>
  <a id="2344" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2242" class="Function">map-strictly-inflationary-map-Strict-Preorder</a> <a id="2390" class="Symbol">=</a>
    <a id="2396" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2400" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2182" class="Bound">f</a>

  <a id="2405" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2405" class="Function">is-inflationary-strictly-inflationary-map-Strict-Preorder</a> <a id="2463" class="Symbol">:</a>
    <a id="2469" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1389" class="Function">is-strictly-inflationary-map-Strict-Preorder</a> <a id="2514" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2152" class="Bound">P</a>
      <a id="2522" class="Symbol">(</a> <a id="2524" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2242" class="Function">map-strictly-inflationary-map-Strict-Preorder</a><a id="2569" class="Symbol">)</a>
  <a id="2573" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2405" class="Function">is-inflationary-strictly-inflationary-map-Strict-Preorder</a> <a id="2631" class="Symbol">=</a>
    <a id="2637" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2641" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2182" class="Bound">f</a>
</pre>
### The predicate on order preserving maps of being inflationary

<pre class="Agda"><a id="2722" class="Keyword">module</a> <a id="2729" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2729" class="Module">_</a>
  <a id="2733" class="Symbol">{</a><a id="2734" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2734" class="Bound">l1</a> <a id="2737" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2737" class="Bound">l2</a> <a id="2740" class="Symbol">:</a> <a id="2742" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2747" class="Symbol">}</a> <a id="2749" class="Symbol">(</a><a id="2750" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2750" class="Bound">P</a> <a id="2752" class="Symbol">:</a> <a id="2754" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="2770" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2734" class="Bound">l1</a> <a id="2773" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2737" class="Bound">l2</a><a id="2775" class="Symbol">)</a>
  <a id="2779" class="Symbol">(</a><a id="2780" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2780" class="Bound">f</a> <a id="2782" class="Symbol">:</a> <a id="2784" href="order-theory.strict-order-preserving-maps.html#2072" class="Function">hom-Strict-Preorder</a> <a id="2804" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2750" class="Bound">P</a> <a id="2806" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2750" class="Bound">P</a><a id="2807" class="Symbol">)</a>
  <a id="2811" class="Keyword">where</a>

  <a id="2820" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2820" class="Function">is-inflationary-prop-hom-Strict-Preorder</a> <a id="2861" class="Symbol">:</a>
    <a id="2867" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2872" class="Symbol">(</a><a id="2873" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2734" class="Bound">l1</a> <a id="2876" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2878" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2737" class="Bound">l2</a><a id="2880" class="Symbol">)</a>
  <a id="2884" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2820" class="Function">is-inflationary-prop-hom-Strict-Preorder</a> <a id="2925" class="Symbol">=</a>
    <a id="2931" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1169" class="Function">is-strictly-inflationary-map-prop-Strict-Preorder</a> <a id="2981" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2750" class="Bound">P</a>
      <a id="2989" class="Symbol">(</a> <a id="2991" href="order-theory.strict-order-preserving-maps.html#2347" class="Function">map-hom-Strict-Preorder</a> <a id="3015" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2750" class="Bound">P</a> <a id="3017" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2750" class="Bound">P</a> <a id="3019" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2780" class="Bound">f</a><a id="3020" class="Symbol">)</a>

  <a id="3025" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3025" class="Function">is-inflationary-hom-Strict-Preorder</a> <a id="3061" class="Symbol">:</a>
    <a id="3067" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3070" class="Symbol">(</a><a id="3071" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2734" class="Bound">l1</a> <a id="3074" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3076" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2737" class="Bound">l2</a><a id="3078" class="Symbol">)</a>
  <a id="3082" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3025" class="Function">is-inflationary-hom-Strict-Preorder</a> <a id="3118" class="Symbol">=</a>
    <a id="3124" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1389" class="Function">is-strictly-inflationary-map-Strict-Preorder</a> <a id="3169" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2750" class="Bound">P</a>
      <a id="3177" class="Symbol">(</a> <a id="3179" href="order-theory.strict-order-preserving-maps.html#2347" class="Function">map-hom-Strict-Preorder</a> <a id="3203" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2750" class="Bound">P</a> <a id="3205" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2750" class="Bound">P</a> <a id="3207" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2780" class="Bound">f</a><a id="3208" class="Symbol">)</a>

  <a id="3213" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3213" class="Function">is-prop-is-inflationary-hom-Strict-Preorder</a> <a id="3257" class="Symbol">:</a>
    <a id="3263" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="3271" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3025" class="Function">is-inflationary-hom-Strict-Preorder</a>
  <a id="3309" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3213" class="Function">is-prop-is-inflationary-hom-Strict-Preorder</a> <a id="3353" class="Symbol">=</a>
    <a id="3359" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1569" class="Function">is-prop-is-strictly-inflationary-map-Strict-Preorder</a> <a id="3412" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2750" class="Bound">P</a>
      <a id="3420" class="Symbol">(</a> <a id="3422" href="order-theory.strict-order-preserving-maps.html#2347" class="Function">map-hom-Strict-Preorder</a> <a id="3446" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2750" class="Bound">P</a> <a id="3448" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2750" class="Bound">P</a> <a id="3450" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2780" class="Bound">f</a><a id="3451" class="Symbol">)</a>
</pre>
### The type of inflationary morphisms on a strict preorder

<pre class="Agda"><a id="3527" class="Keyword">module</a> <a id="3534" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3534" class="Module">_</a>
  <a id="3538" class="Symbol">{</a><a id="3539" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3539" class="Bound">l1</a> <a id="3542" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3542" class="Bound">l2</a> <a id="3545" class="Symbol">:</a> <a id="3547" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3552" class="Symbol">}</a> <a id="3554" class="Symbol">(</a><a id="3555" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3555" class="Bound">P</a> <a id="3557" class="Symbol">:</a> <a id="3559" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="3575" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3539" class="Bound">l1</a> <a id="3578" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3542" class="Bound">l2</a><a id="3580" class="Symbol">)</a>
  <a id="3584" class="Keyword">where</a>

  <a id="3593" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3593" class="Function">inflationary-hom-Strict-Preorder</a> <a id="3626" class="Symbol">:</a>
    <a id="3632" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3635" class="Symbol">(</a><a id="3636" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3539" class="Bound">l1</a> <a id="3639" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3641" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3542" class="Bound">l2</a><a id="3643" class="Symbol">)</a>
  <a id="3647" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3593" class="Function">inflationary-hom-Strict-Preorder</a> <a id="3680" class="Symbol">=</a>
    <a id="3686" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="3699" class="Symbol">(</a><a id="3700" href="order-theory.strictly-inflationary-maps-strict-preorders.html#2820" class="Function">is-inflationary-prop-hom-Strict-Preorder</a> <a id="3741" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3555" class="Bound">P</a><a id="3742" class="Symbol">)</a>

<a id="3745" class="Keyword">module</a> <a id="3752" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3752" class="Module">_</a>
  <a id="3756" class="Symbol">{</a><a id="3757" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3757" class="Bound">l1</a> <a id="3760" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3760" class="Bound">l2</a> <a id="3763" class="Symbol">:</a> <a id="3765" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3770" class="Symbol">}</a> <a id="3772" class="Symbol">(</a><a id="3773" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3773" class="Bound">P</a> <a id="3775" class="Symbol">:</a> <a id="3777" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="3793" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3757" class="Bound">l1</a> <a id="3796" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3760" class="Bound">l2</a><a id="3798" class="Symbol">)</a>
  <a id="3802" class="Symbol">(</a><a id="3803" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3803" class="Bound">f</a> <a id="3805" class="Symbol">:</a> <a id="3807" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3593" class="Function">inflationary-hom-Strict-Preorder</a> <a id="3840" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3773" class="Bound">P</a><a id="3841" class="Symbol">)</a>
  <a id="3845" class="Keyword">where</a>

  <a id="3854" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3854" class="Function">hom-inflationary-hom-Strict-Preorder</a> <a id="3891" class="Symbol">:</a>
    <a id="3897" href="order-theory.strict-order-preserving-maps.html#2072" class="Function">hom-Strict-Preorder</a> <a id="3917" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3773" class="Bound">P</a> <a id="3919" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3773" class="Bound">P</a>
  <a id="3923" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3854" class="Function">hom-inflationary-hom-Strict-Preorder</a> <a id="3960" class="Symbol">=</a>
    <a id="3966" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3970" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3803" class="Bound">f</a>

  <a id="3975" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3975" class="Function">map-inflationary-hom-Strict-Preorder</a> <a id="4012" class="Symbol">:</a>
    <a id="4018" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a> <a id="4039" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3773" class="Bound">P</a> <a id="4041" class="Symbol">→</a> <a id="4043" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a> <a id="4064" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3773" class="Bound">P</a>
  <a id="4068" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3975" class="Function">map-inflationary-hom-Strict-Preorder</a> <a id="4105" class="Symbol">=</a>
    <a id="4111" href="order-theory.strict-order-preserving-maps.html#2347" class="Function">map-hom-Strict-Preorder</a> <a id="4135" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3773" class="Bound">P</a> <a id="4137" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3773" class="Bound">P</a>
      <a id="4145" class="Symbol">(</a> <a id="4147" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3854" class="Function">hom-inflationary-hom-Strict-Preorder</a><a id="4183" class="Symbol">)</a>

  <a id="4188" href="order-theory.strictly-inflationary-maps-strict-preorders.html#4188" class="Function">preserves-order-inflationary-hom-Strict-Preorder</a> <a id="4237" class="Symbol">:</a>
    <a id="4243" href="order-theory.strict-order-preserving-maps.html#1474" class="Function">preserves-strict-order-map-Strict-Preorder</a> <a id="4286" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3773" class="Bound">P</a> <a id="4288" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3773" class="Bound">P</a>
      <a id="4296" class="Symbol">(</a> <a id="4298" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3975" class="Function">map-inflationary-hom-Strict-Preorder</a><a id="4334" class="Symbol">)</a>
  <a id="4338" href="order-theory.strictly-inflationary-maps-strict-preorders.html#4188" class="Function">preserves-order-inflationary-hom-Strict-Preorder</a> <a id="4387" class="Symbol">=</a>
    <a id="4393" href="order-theory.strict-order-preserving-maps.html#2466" class="Function">preserves-strict-order-hom-Strict-Preorder</a> <a id="4436" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3773" class="Bound">P</a> <a id="4438" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3773" class="Bound">P</a>
      <a id="4446" class="Symbol">(</a> <a id="4448" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3854" class="Function">hom-inflationary-hom-Strict-Preorder</a><a id="4484" class="Symbol">)</a>

  <a id="4489" href="order-theory.strictly-inflationary-maps-strict-preorders.html#4489" class="Function">is-inflationary-inflationary-hom-Strict-Preorder</a> <a id="4538" class="Symbol">:</a>
    <a id="4544" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1389" class="Function">is-strictly-inflationary-map-Strict-Preorder</a> <a id="4589" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3773" class="Bound">P</a>
      <a id="4597" class="Symbol">(</a> <a id="4599" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3975" class="Function">map-inflationary-hom-Strict-Preorder</a><a id="4635" class="Symbol">)</a>
  <a id="4639" href="order-theory.strictly-inflationary-maps-strict-preorders.html#4489" class="Function">is-inflationary-inflationary-hom-Strict-Preorder</a> <a id="4688" class="Symbol">=</a>
    <a id="4694" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4698" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3803" class="Bound">f</a>

  <a id="4703" href="order-theory.strictly-inflationary-maps-strict-preorders.html#4703" class="Function">inflationary-map-inflationary-hom-Strict-Preorder</a> <a id="4753" class="Symbol">:</a>
    <a id="4759" href="order-theory.strictly-inflationary-maps-strict-preorders.html#1945" class="Function">strictly-inflationary-map-Strict-Preorder</a> <a id="4801" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3773" class="Bound">P</a>
  <a id="4805" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4809" href="order-theory.strictly-inflationary-maps-strict-preorders.html#4703" class="Function">inflationary-map-inflationary-hom-Strict-Preorder</a> <a id="4859" class="Symbol">=</a>
    <a id="4865" href="order-theory.strictly-inflationary-maps-strict-preorders.html#3975" class="Function">map-inflationary-hom-Strict-Preorder</a>
  <a id="4904" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4908" href="order-theory.strictly-inflationary-maps-strict-preorders.html#4703" class="Function">inflationary-map-inflationary-hom-Strict-Preorder</a> <a id="4958" class="Symbol">=</a>
    <a id="4964" href="order-theory.strictly-inflationary-maps-strict-preorders.html#4489" class="Function">is-inflationary-inflationary-hom-Strict-Preorder</a>
</pre>