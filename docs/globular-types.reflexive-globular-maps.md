# Reflexive globular maps

<pre class="Agda"><a id="36" class="Symbol">{-#</a> <a id="40" class="Keyword">OPTIONS</a> <a id="48" class="Pragma">--guardedness</a> <a id="62" class="Symbol">#-}</a>

<a id="67" class="Keyword">module</a> <a id="74" href="globular-types.reflexive-globular-maps.html" class="Module">globular-types.reflexive-globular-maps</a> <a id="113" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="169" class="Keyword">open</a> <a id="174" class="Keyword">import</a> <a id="181" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="207" class="Keyword">open</a> <a id="212" class="Keyword">import</a> <a id="219" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="globular-types.globular-maps.html" class="Module">globular-types.globular-maps</a>
<a id="288" class="Keyword">open</a> <a id="293" class="Keyword">import</a> <a id="300" href="globular-types.reflexive-globular-types.html" class="Module">globular-types.reflexive-globular-types</a>
</pre>
</details>

## Idea

A {{#concept "reflexive globular map" Agda=reflexive-globular-map}} between two
[reflexive globular types](globular-types.reflexive-globular-types.md) `G` and
`H` is a [globular map](globular-types.globular-maps.md) `f : G → H` equipped
with a family of [identifications](foundation-core.identity-types.md)

```text
  (x : G₀) → f₁ (refl G x) ＝ refl H (f₀ x)
```

from the image of the reflexivity cell at `x` in `G` to the reflexivity cell at
`f₀ x`, such that the globular map `f' : G' x y → H' (f₀ x) (f₀ y)` is again
reflexive.

Note: In some settings it may be preferred to work with globular maps preserving
reflexivity cells up to a higher cell. The two notions of maps between reflexive
globular types preserving the reflexivity structure up to a higher cell are,
depending of the direction of the coherence cells, the notions of
[colax reflexive globular maps](globular-types.colax-reflexive-globular-maps.md)
and
[lax reflexive globular maps](globular-types.lax-reflexive-globular-maps.md).

## Definitions

### The predicate of preserving reflexivity

<pre class="Agda"><a id="1437" class="Keyword">record</a>
  <a id="preserves-refl-globular-map"></a><a id="1446" href="globular-types.reflexive-globular-maps.html#1446" class="Record">preserves-refl-globular-map</a>
    <a id="1478" class="Symbol">{</a><a id="1479" href="globular-types.reflexive-globular-maps.html#1479" class="Bound">l1</a> <a id="1482" href="globular-types.reflexive-globular-maps.html#1482" class="Bound">l2</a> <a id="1485" href="globular-types.reflexive-globular-maps.html#1485" class="Bound">l3</a> <a id="1488" href="globular-types.reflexive-globular-maps.html#1488" class="Bound">l4</a> <a id="1491" class="Symbol">:</a> <a id="1493" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1498" class="Symbol">}</a>
    <a id="1504" class="Symbol">(</a><a id="1505" href="globular-types.reflexive-globular-maps.html#1505" class="Bound">G</a> <a id="1507" class="Symbol">:</a> <a id="1509" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="1533" href="globular-types.reflexive-globular-maps.html#1479" class="Bound">l1</a> <a id="1536" href="globular-types.reflexive-globular-maps.html#1482" class="Bound">l2</a><a id="1538" class="Symbol">)</a> <a id="1540" class="Symbol">(</a><a id="1541" href="globular-types.reflexive-globular-maps.html#1541" class="Bound">H</a> <a id="1543" class="Symbol">:</a> <a id="1545" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="1569" href="globular-types.reflexive-globular-maps.html#1485" class="Bound">l3</a> <a id="1572" href="globular-types.reflexive-globular-maps.html#1488" class="Bound">l4</a><a id="1574" class="Symbol">)</a>
    <a id="1580" class="Symbol">(</a><a id="1581" href="globular-types.reflexive-globular-maps.html#1581" class="Bound">f</a> <a id="1583" class="Symbol">:</a> <a id="1585" href="globular-types.reflexive-globular-types.html#10403" class="Function">globular-map-Reflexive-Globular-Type</a> <a id="1622" href="globular-types.reflexive-globular-maps.html#1505" class="Bound">G</a> <a id="1624" href="globular-types.reflexive-globular-maps.html#1541" class="Bound">H</a><a id="1625" class="Symbol">)</a> <a id="1627" class="Symbol">:</a>
    <a id="1633" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1636" class="Symbol">(</a><a id="1637" href="globular-types.reflexive-globular-maps.html#1479" class="Bound">l1</a> <a id="1640" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1642" href="globular-types.reflexive-globular-maps.html#1482" class="Bound">l2</a> <a id="1645" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1647" href="globular-types.reflexive-globular-maps.html#1488" class="Bound">l4</a><a id="1649" class="Symbol">)</a>
  <a id="1653" class="Keyword">where</a>
  <a id="1661" class="Keyword">coinductive</a>

  <a id="1676" class="Keyword">field</a>
    <a id="preserves-refl-globular-map.preserves-refl-1-cell-preserves-refl-globular-map"></a><a id="1686" href="globular-types.reflexive-globular-maps.html#1686" class="Field">preserves-refl-1-cell-preserves-refl-globular-map</a> <a id="1736" class="Symbol">:</a>
      <a id="1744" class="Symbol">(</a><a id="1745" href="globular-types.reflexive-globular-maps.html#1745" class="Bound">x</a> <a id="1747" class="Symbol">:</a> <a id="1749" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="1780" href="globular-types.reflexive-globular-maps.html#1505" class="Bound">G</a><a id="1781" class="Symbol">)</a> <a id="1783" class="Symbol">→</a>
      <a id="1791" href="globular-types.globular-maps.html#1422" class="Function">1-cell-globular-map</a> <a id="1811" href="globular-types.reflexive-globular-maps.html#1581" class="Bound">f</a> <a id="1813" class="Symbol">(</a><a id="1814" href="globular-types.reflexive-globular-types.html#5428" class="Function">refl-1-cell-Reflexive-Globular-Type</a> <a id="1850" href="globular-types.reflexive-globular-maps.html#1505" class="Bound">G</a> <a id="1852" class="Symbol">{</a><a id="1853" href="globular-types.reflexive-globular-maps.html#1745" class="Bound">x</a><a id="1854" class="Symbol">})</a> <a id="1857" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
      <a id="1865" href="globular-types.reflexive-globular-types.html#5428" class="Function">refl-1-cell-Reflexive-Globular-Type</a> <a id="1901" href="globular-types.reflexive-globular-maps.html#1541" class="Bound">H</a>

  <a id="1906" class="Keyword">field</a>
    <a id="preserves-refl-globular-map.preserves-refl-1-cell-globular-map-preserves-refl-globular-map"></a><a id="1916" href="globular-types.reflexive-globular-maps.html#1916" class="Field">preserves-refl-1-cell-globular-map-preserves-refl-globular-map</a> <a id="1979" class="Symbol">:</a>
      <a id="1987" class="Symbol">{</a><a id="1988" href="globular-types.reflexive-globular-maps.html#1988" class="Bound">x</a> <a id="1990" href="globular-types.reflexive-globular-maps.html#1990" class="Bound">y</a> <a id="1992" class="Symbol">:</a> <a id="1994" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="2025" href="globular-types.reflexive-globular-maps.html#1505" class="Bound">G</a><a id="2026" class="Symbol">}</a> <a id="2028" class="Symbol">→</a>
      <a id="2036" href="globular-types.reflexive-globular-maps.html#1446" class="Record">preserves-refl-globular-map</a>
        <a id="2072" class="Symbol">(</a> <a id="2074" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="2129" href="globular-types.reflexive-globular-maps.html#1505" class="Bound">G</a> <a id="2131" href="globular-types.reflexive-globular-maps.html#1988" class="Bound">x</a> <a id="2133" href="globular-types.reflexive-globular-maps.html#1990" class="Bound">y</a><a id="2134" class="Symbol">)</a>
        <a id="2144" class="Symbol">(</a> <a id="2146" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="2201" href="globular-types.reflexive-globular-maps.html#1541" class="Bound">H</a> <a id="2203" class="Symbol">_</a> <a id="2205" class="Symbol">_)</a>
        <a id="2216" class="Symbol">(</a> <a id="2218" href="globular-types.reflexive-globular-types.html#10984" class="Function">1-cell-globular-map-globular-map-Reflexive-Globular-Type</a> <a id="2275" href="globular-types.reflexive-globular-maps.html#1505" class="Bound">G</a> <a id="2277" href="globular-types.reflexive-globular-maps.html#1541" class="Bound">H</a> <a id="2279" href="globular-types.reflexive-globular-maps.html#1581" class="Bound">f</a><a id="2280" class="Symbol">)</a>

<a id="2283" class="Keyword">open</a> <a id="2288" href="globular-types.reflexive-globular-maps.html#1446" class="Module">preserves-refl-globular-map</a> <a id="2316" class="Keyword">public</a>
</pre>
### Reflexive globular maps

<pre class="Agda"><a id="2365" class="Keyword">record</a>
  <a id="reflexive-globular-map"></a><a id="2374" href="globular-types.reflexive-globular-maps.html#2374" class="Record">reflexive-globular-map</a>
    <a id="2401" class="Symbol">{</a><a id="2402" href="globular-types.reflexive-globular-maps.html#2402" class="Bound">l1</a> <a id="2405" href="globular-types.reflexive-globular-maps.html#2405" class="Bound">l2</a> <a id="2408" href="globular-types.reflexive-globular-maps.html#2408" class="Bound">l3</a> <a id="2411" href="globular-types.reflexive-globular-maps.html#2411" class="Bound">l4</a> <a id="2414" class="Symbol">:</a> <a id="2416" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2421" class="Symbol">}</a>
    <a id="2427" class="Symbol">(</a><a id="2428" href="globular-types.reflexive-globular-maps.html#2428" class="Bound">G</a> <a id="2430" class="Symbol">:</a> <a id="2432" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="2456" href="globular-types.reflexive-globular-maps.html#2402" class="Bound">l1</a> <a id="2459" href="globular-types.reflexive-globular-maps.html#2405" class="Bound">l2</a><a id="2461" class="Symbol">)</a>
    <a id="2467" class="Symbol">(</a><a id="2468" href="globular-types.reflexive-globular-maps.html#2468" class="Bound">H</a> <a id="2470" class="Symbol">:</a> <a id="2472" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="2496" href="globular-types.reflexive-globular-maps.html#2408" class="Bound">l3</a> <a id="2499" href="globular-types.reflexive-globular-maps.html#2411" class="Bound">l4</a><a id="2501" class="Symbol">)</a> <a id="2503" class="Symbol">:</a>
    <a id="2509" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2512" class="Symbol">(</a><a id="2513" href="globular-types.reflexive-globular-maps.html#2402" class="Bound">l1</a> <a id="2516" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2518" href="globular-types.reflexive-globular-maps.html#2405" class="Bound">l2</a> <a id="2521" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2523" href="globular-types.reflexive-globular-maps.html#2408" class="Bound">l3</a> <a id="2526" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2528" href="globular-types.reflexive-globular-maps.html#2411" class="Bound">l4</a><a id="2530" class="Symbol">)</a>
  <a id="2534" class="Keyword">where</a>

  <a id="2543" class="Keyword">field</a>
    <a id="reflexive-globular-map.globular-map-reflexive-globular-map"></a><a id="2553" href="globular-types.reflexive-globular-maps.html#2553" class="Field">globular-map-reflexive-globular-map</a> <a id="2589" class="Symbol">:</a>
      <a id="2597" href="globular-types.reflexive-globular-types.html#10403" class="Function">globular-map-Reflexive-Globular-Type</a> <a id="2634" href="globular-types.reflexive-globular-maps.html#2428" class="Bound">G</a> <a id="2636" href="globular-types.reflexive-globular-maps.html#2468" class="Bound">H</a>

  <a id="reflexive-globular-map.0-cell-reflexive-globular-map"></a><a id="2641" href="globular-types.reflexive-globular-maps.html#2641" class="Function">0-cell-reflexive-globular-map</a> <a id="2671" class="Symbol">:</a>
    <a id="2677" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="2708" href="globular-types.reflexive-globular-maps.html#2428" class="Bound">G</a> <a id="2710" class="Symbol">→</a> <a id="2712" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="2743" href="globular-types.reflexive-globular-maps.html#2468" class="Bound">H</a>
  <a id="2747" href="globular-types.reflexive-globular-maps.html#2641" class="Function">0-cell-reflexive-globular-map</a> <a id="2777" class="Symbol">=</a>
    <a id="2783" href="globular-types.globular-maps.html#928" class="Field">0-cell-globular-map</a> <a id="2803" href="globular-types.reflexive-globular-maps.html#2553" class="Field">globular-map-reflexive-globular-map</a>

  <a id="reflexive-globular-map.1-cell-reflexive-globular-map"></a><a id="2842" href="globular-types.reflexive-globular-maps.html#2842" class="Function">1-cell-reflexive-globular-map</a> <a id="2872" class="Symbol">:</a>
    <a id="2878" class="Symbol">{</a><a id="2879" href="globular-types.reflexive-globular-maps.html#2879" class="Bound">x</a> <a id="2881" href="globular-types.reflexive-globular-maps.html#2881" class="Bound">y</a> <a id="2883" class="Symbol">:</a> <a id="2885" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="2916" href="globular-types.reflexive-globular-maps.html#2428" class="Bound">G</a><a id="2917" class="Symbol">}</a> <a id="2919" class="Symbol">→</a>
    <a id="2925" href="globular-types.reflexive-globular-types.html#4270" class="Function">1-cell-Reflexive-Globular-Type</a> <a id="2956" href="globular-types.reflexive-globular-maps.html#2428" class="Bound">G</a> <a id="2958" href="globular-types.reflexive-globular-maps.html#2879" class="Bound">x</a> <a id="2960" href="globular-types.reflexive-globular-maps.html#2881" class="Bound">y</a> <a id="2962" class="Symbol">→</a>
    <a id="2968" href="globular-types.reflexive-globular-types.html#4270" class="Function">1-cell-Reflexive-Globular-Type</a> <a id="2999" href="globular-types.reflexive-globular-maps.html#2468" class="Bound">H</a>
      <a id="3007" class="Symbol">(</a> <a id="3009" href="globular-types.reflexive-globular-maps.html#2641" class="Function">0-cell-reflexive-globular-map</a> <a id="3039" href="globular-types.reflexive-globular-maps.html#2879" class="Bound">x</a><a id="3040" class="Symbol">)</a>
      <a id="3048" class="Symbol">(</a> <a id="3050" href="globular-types.reflexive-globular-maps.html#2641" class="Function">0-cell-reflexive-globular-map</a> <a id="3080" href="globular-types.reflexive-globular-maps.html#2881" class="Bound">y</a><a id="3081" class="Symbol">)</a>
  <a id="3085" href="globular-types.reflexive-globular-maps.html#2842" class="Function">1-cell-reflexive-globular-map</a> <a id="3115" class="Symbol">=</a>
    <a id="3121" href="globular-types.globular-maps.html#1422" class="Function">1-cell-globular-map</a> <a id="3141" href="globular-types.reflexive-globular-maps.html#2553" class="Field">globular-map-reflexive-globular-map</a>

  <a id="reflexive-globular-map.1-cell-globular-map-reflexive-globular-map"></a><a id="3180" href="globular-types.reflexive-globular-maps.html#3180" class="Function">1-cell-globular-map-reflexive-globular-map</a> <a id="3223" class="Symbol">:</a>
    <a id="3229" class="Symbol">{</a><a id="3230" href="globular-types.reflexive-globular-maps.html#3230" class="Bound">x</a> <a id="3232" href="globular-types.reflexive-globular-maps.html#3232" class="Bound">y</a> <a id="3234" class="Symbol">:</a> <a id="3236" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="3267" href="globular-types.reflexive-globular-maps.html#2428" class="Bound">G</a><a id="3268" class="Symbol">}</a> <a id="3270" class="Symbol">→</a>
    <a id="3276" href="globular-types.reflexive-globular-types.html#10403" class="Function">globular-map-Reflexive-Globular-Type</a>
      <a id="3319" class="Symbol">(</a> <a id="3321" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="3376" href="globular-types.reflexive-globular-maps.html#2428" class="Bound">G</a> <a id="3378" href="globular-types.reflexive-globular-maps.html#3230" class="Bound">x</a> <a id="3380" href="globular-types.reflexive-globular-maps.html#3232" class="Bound">y</a><a id="3381" class="Symbol">)</a>
      <a id="3389" class="Symbol">(</a> <a id="3391" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="3446" href="globular-types.reflexive-globular-maps.html#2468" class="Bound">H</a>
        <a id="3456" class="Symbol">(</a> <a id="3458" href="globular-types.reflexive-globular-maps.html#2641" class="Function">0-cell-reflexive-globular-map</a> <a id="3488" href="globular-types.reflexive-globular-maps.html#3230" class="Bound">x</a><a id="3489" class="Symbol">)</a>
        <a id="3499" class="Symbol">(</a> <a id="3501" href="globular-types.reflexive-globular-maps.html#2641" class="Function">0-cell-reflexive-globular-map</a> <a id="3531" href="globular-types.reflexive-globular-maps.html#3232" class="Bound">y</a><a id="3532" class="Symbol">))</a>
  <a id="3537" href="globular-types.reflexive-globular-maps.html#3180" class="Function">1-cell-globular-map-reflexive-globular-map</a> <a id="3580" class="Symbol">=</a>
    <a id="3586" href="globular-types.globular-maps.html#1009" class="Field">1-cell-globular-map-globular-map</a> <a id="3619" href="globular-types.reflexive-globular-maps.html#2553" class="Field">globular-map-reflexive-globular-map</a>

  <a id="3658" class="Keyword">field</a>
    <a id="reflexive-globular-map.preserves-refl-reflexive-globular-map"></a><a id="3668" href="globular-types.reflexive-globular-maps.html#3668" class="Field">preserves-refl-reflexive-globular-map</a> <a id="3706" class="Symbol">:</a>
      <a id="3714" href="globular-types.reflexive-globular-maps.html#1446" class="Record">preserves-refl-globular-map</a> <a id="3742" href="globular-types.reflexive-globular-maps.html#2428" class="Bound">G</a> <a id="3744" href="globular-types.reflexive-globular-maps.html#2468" class="Bound">H</a>
        <a id="3754" href="globular-types.reflexive-globular-maps.html#2553" class="Field">globular-map-reflexive-globular-map</a>

  <a id="reflexive-globular-map.preserves-refl-1-cell-reflexive-globular-map"></a><a id="3793" href="globular-types.reflexive-globular-maps.html#3793" class="Function">preserves-refl-1-cell-reflexive-globular-map</a> <a id="3838" class="Symbol">:</a>
    <a id="3844" class="Symbol">(</a> <a id="3846" href="globular-types.reflexive-globular-maps.html#3846" class="Bound">x</a> <a id="3848" class="Symbol">:</a> <a id="3850" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="3881" href="globular-types.reflexive-globular-maps.html#2428" class="Bound">G</a><a id="3882" class="Symbol">)</a> <a id="3884" class="Symbol">→</a>
    <a id="3890" href="globular-types.reflexive-globular-maps.html#2842" class="Function">1-cell-reflexive-globular-map</a> <a id="3920" class="Symbol">(</a><a id="3921" href="globular-types.reflexive-globular-types.html#5428" class="Function">refl-1-cell-Reflexive-Globular-Type</a> <a id="3957" href="globular-types.reflexive-globular-maps.html#2428" class="Bound">G</a> <a id="3959" class="Symbol">{</a><a id="3960" href="globular-types.reflexive-globular-maps.html#3846" class="Bound">x</a><a id="3961" class="Symbol">})</a> <a id="3964" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="3970" href="globular-types.reflexive-globular-types.html#5428" class="Function">refl-1-cell-Reflexive-Globular-Type</a> <a id="4006" href="globular-types.reflexive-globular-maps.html#2468" class="Bound">H</a>
  <a id="4010" href="globular-types.reflexive-globular-maps.html#3793" class="Function">preserves-refl-1-cell-reflexive-globular-map</a> <a id="4055" class="Symbol">=</a>
    <a id="4061" href="globular-types.reflexive-globular-maps.html#1686" class="Field">preserves-refl-1-cell-preserves-refl-globular-map</a>
      <a id="4117" href="globular-types.reflexive-globular-maps.html#3668" class="Field">preserves-refl-reflexive-globular-map</a>

  <a id="reflexive-globular-map.preserves-refl-2-cell-globular-map-reflexive-globular-map"></a><a id="4158" href="globular-types.reflexive-globular-maps.html#4158" class="Function">preserves-refl-2-cell-globular-map-reflexive-globular-map</a> <a id="4216" class="Symbol">:</a>
    <a id="4222" class="Symbol">{</a> <a id="4224" href="globular-types.reflexive-globular-maps.html#4224" class="Bound">x</a> <a id="4226" href="globular-types.reflexive-globular-maps.html#4226" class="Bound">y</a> <a id="4228" class="Symbol">:</a> <a id="4230" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="4261" href="globular-types.reflexive-globular-maps.html#2428" class="Bound">G</a><a id="4262" class="Symbol">}</a> <a id="4264" class="Symbol">→</a>
    <a id="4270" href="globular-types.reflexive-globular-maps.html#1446" class="Record">preserves-refl-globular-map</a>
      <a id="4304" class="Symbol">(</a> <a id="4306" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="4361" href="globular-types.reflexive-globular-maps.html#2428" class="Bound">G</a> <a id="4363" href="globular-types.reflexive-globular-maps.html#4224" class="Bound">x</a> <a id="4365" href="globular-types.reflexive-globular-maps.html#4226" class="Bound">y</a><a id="4366" class="Symbol">)</a>
      <a id="4374" class="Symbol">(</a> <a id="4376" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="4431" href="globular-types.reflexive-globular-maps.html#2468" class="Bound">H</a>
        <a id="4441" class="Symbol">(</a> <a id="4443" href="globular-types.reflexive-globular-maps.html#2641" class="Function">0-cell-reflexive-globular-map</a> <a id="4473" href="globular-types.reflexive-globular-maps.html#4224" class="Bound">x</a><a id="4474" class="Symbol">)</a>
        <a id="4484" class="Symbol">(</a> <a id="4486" href="globular-types.reflexive-globular-maps.html#2641" class="Function">0-cell-reflexive-globular-map</a> <a id="4516" href="globular-types.reflexive-globular-maps.html#4226" class="Bound">y</a><a id="4517" class="Symbol">))</a>
      <a id="4526" class="Symbol">(</a> <a id="4528" href="globular-types.reflexive-globular-maps.html#3180" class="Function">1-cell-globular-map-reflexive-globular-map</a><a id="4570" class="Symbol">)</a>
  <a id="4574" href="globular-types.reflexive-globular-maps.html#4158" class="Function">preserves-refl-2-cell-globular-map-reflexive-globular-map</a> <a id="4632" class="Symbol">=</a>
    <a id="4638" href="globular-types.reflexive-globular-maps.html#1916" class="Field">preserves-refl-1-cell-globular-map-preserves-refl-globular-map</a>
      <a id="4707" href="globular-types.reflexive-globular-maps.html#3668" class="Field">preserves-refl-reflexive-globular-map</a>

  <a id="reflexive-globular-map.1-cell-reflexive-globular-map-reflexive-globular-map"></a><a id="4748" href="globular-types.reflexive-globular-maps.html#4748" class="Function">1-cell-reflexive-globular-map-reflexive-globular-map</a> <a id="4801" class="Symbol">:</a>
    <a id="4807" class="Symbol">{</a><a id="4808" href="globular-types.reflexive-globular-maps.html#4808" class="Bound">x</a> <a id="4810" href="globular-types.reflexive-globular-maps.html#4810" class="Bound">y</a> <a id="4812" class="Symbol">:</a> <a id="4814" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="4845" href="globular-types.reflexive-globular-maps.html#2428" class="Bound">G</a><a id="4846" class="Symbol">}</a> <a id="4848" class="Symbol">→</a>
    <a id="4854" href="globular-types.reflexive-globular-maps.html#2374" class="Record">reflexive-globular-map</a>
      <a id="4883" class="Symbol">(</a> <a id="4885" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="4940" href="globular-types.reflexive-globular-maps.html#2428" class="Bound">G</a> <a id="4942" href="globular-types.reflexive-globular-maps.html#4808" class="Bound">x</a> <a id="4944" href="globular-types.reflexive-globular-maps.html#4810" class="Bound">y</a><a id="4945" class="Symbol">)</a>
      <a id="4953" class="Symbol">(</a> <a id="4955" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="5010" href="globular-types.reflexive-globular-maps.html#2468" class="Bound">H</a>
        <a id="5020" class="Symbol">(</a> <a id="5022" href="globular-types.reflexive-globular-maps.html#2641" class="Function">0-cell-reflexive-globular-map</a> <a id="5052" href="globular-types.reflexive-globular-maps.html#4808" class="Bound">x</a><a id="5053" class="Symbol">)</a>
        <a id="5063" class="Symbol">(</a> <a id="5065" href="globular-types.reflexive-globular-maps.html#2641" class="Function">0-cell-reflexive-globular-map</a> <a id="5095" href="globular-types.reflexive-globular-maps.html#4810" class="Bound">y</a><a id="5096" class="Symbol">))</a>
  <a id="5101" href="globular-types.reflexive-globular-maps.html#2553" class="Field">globular-map-reflexive-globular-map</a>
    <a id="5141" href="globular-types.reflexive-globular-maps.html#4748" class="Function">1-cell-reflexive-globular-map-reflexive-globular-map</a> <a id="5194" class="Symbol">=</a>
    <a id="5200" href="globular-types.reflexive-globular-maps.html#3180" class="Function">1-cell-globular-map-reflexive-globular-map</a>
  <a id="5245" href="globular-types.reflexive-globular-maps.html#3668" class="Field">preserves-refl-reflexive-globular-map</a>
    <a id="5287" href="globular-types.reflexive-globular-maps.html#4748" class="Function">1-cell-reflexive-globular-map-reflexive-globular-map</a> <a id="5340" class="Symbol">=</a>
    <a id="5346" href="globular-types.reflexive-globular-maps.html#4158" class="Function">preserves-refl-2-cell-globular-map-reflexive-globular-map</a>

<a id="5405" class="Keyword">open</a> <a id="5410" href="globular-types.reflexive-globular-maps.html#2374" class="Module">reflexive-globular-map</a> <a id="5433" class="Keyword">public</a>
</pre>