# Universal quantification

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="foundation.universal-quantification.html" class="Module">foundation.universal-quantification</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="foundation.evaluation-functions.html" class="Module">foundation.evaluation-functions</a>
<a id="224" class="Keyword">open</a> <a id="229" class="Keyword">import</a> <a id="236" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="268" class="Keyword">open</a> <a id="273" class="Keyword">import</a> <a id="280" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="357" class="Keyword">open</a> <a id="362" class="Keyword">import</a> <a id="369" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="398" class="Keyword">open</a> <a id="403" class="Keyword">import</a> <a id="410" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="441" class="Keyword">open</a> <a id="446" class="Keyword">import</a> <a id="453" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

Given a type `A` and a [subtype](foundation-core.subtypes.md) `P : A → Prop`,
the
{{#concept "universal quantification" Disambiguation="on a subtype" WDID=Q126695 WD="universal quantification"}}

```text
  ∀ (x : A), (P x)
```

is the [proposition](foundation-core.propositions.md) that there exists a proof
of `P x` for every `x` in `A`.

The
{{#concept "universal property" Disambiguation="of universal quantification" Agda=universal-property-for-all}}
of universal quantification states that it is the
[greatest lower bound](order-theory.greatest-lower-bounds-large-posets.md) on
the family of propositions `P` in the
[locale of propositions](foundation.large-locale-of-propositions.md), by which
we mean that for every proposition `Q` we have the
[logical equivalence](foundation.logical-equivalences.md)

```text
  (∀ (a : A), (R → P a)) ↔ (R → ∀ (a : A), (P a))
```

**Notation.** Because of syntactic limitations of the Agda language, we cannot
use `∀` for the universal quantification in formalizations, and instead use
`∀'`.

## Definitions

### Universal quantification

<pre class="Agda"><a id="1597" class="Keyword">module</a> <a id="1604" href="foundation.universal-quantification.html#1604" class="Module">_</a>
  <a id="1608" class="Symbol">{</a><a id="1609" href="foundation.universal-quantification.html#1609" class="Bound">l1</a> <a id="1612" href="foundation.universal-quantification.html#1612" class="Bound">l2</a> <a id="1615" class="Symbol">:</a> <a id="1617" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1622" class="Symbol">}</a> <a id="1624" class="Symbol">(</a><a id="1625" href="foundation.universal-quantification.html#1625" class="Bound">A</a> <a id="1627" class="Symbol">:</a> <a id="1629" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1632" href="foundation.universal-quantification.html#1609" class="Bound">l1</a><a id="1634" class="Symbol">)</a> <a id="1636" class="Symbol">(</a><a id="1637" href="foundation.universal-quantification.html#1637" class="Bound">P</a> <a id="1639" class="Symbol">:</a> <a id="1641" href="foundation.universal-quantification.html#1625" class="Bound">A</a> <a id="1643" class="Symbol">→</a> <a id="1645" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1650" href="foundation.universal-quantification.html#1612" class="Bound">l2</a><a id="1652" class="Symbol">)</a>
  <a id="1656" class="Keyword">where</a>

  <a id="1665" href="foundation.universal-quantification.html#1665" class="Function">for-all-Prop</a> <a id="1678" class="Symbol">:</a> <a id="1680" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1685" class="Symbol">(</a><a id="1686" href="foundation.universal-quantification.html#1609" class="Bound">l1</a> <a id="1689" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1691" href="foundation.universal-quantification.html#1612" class="Bound">l2</a><a id="1693" class="Symbol">)</a>
  <a id="1697" href="foundation.universal-quantification.html#1665" class="Function">for-all-Prop</a> <a id="1710" class="Symbol">=</a> <a id="1712" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="1719" href="foundation.universal-quantification.html#1625" class="Bound">A</a> <a id="1721" href="foundation.universal-quantification.html#1637" class="Bound">P</a>

  <a id="1726" href="foundation.universal-quantification.html#1726" class="Function">type-for-all-Prop</a> <a id="1744" class="Symbol">:</a> <a id="1746" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1749" class="Symbol">(</a><a id="1750" href="foundation.universal-quantification.html#1609" class="Bound">l1</a> <a id="1753" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1755" href="foundation.universal-quantification.html#1612" class="Bound">l2</a><a id="1757" class="Symbol">)</a>
  <a id="1761" href="foundation.universal-quantification.html#1726" class="Function">type-for-all-Prop</a> <a id="1779" class="Symbol">=</a> <a id="1781" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1791" href="foundation.universal-quantification.html#1665" class="Function">for-all-Prop</a>

  <a id="1807" href="foundation.universal-quantification.html#1807" class="Function">is-prop-for-all-Prop</a> <a id="1828" class="Symbol">:</a> <a id="1830" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1838" href="foundation.universal-quantification.html#1726" class="Function">type-for-all-Prop</a>
  <a id="1858" href="foundation.universal-quantification.html#1807" class="Function">is-prop-for-all-Prop</a> <a id="1879" class="Symbol">=</a> <a id="1881" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1899" href="foundation.universal-quantification.html#1665" class="Function">for-all-Prop</a>

  <a id="1915" href="foundation.universal-quantification.html#1915" class="Function">for-all</a> <a id="1923" class="Symbol">:</a> <a id="1925" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1928" class="Symbol">(</a><a id="1929" href="foundation.universal-quantification.html#1609" class="Bound">l1</a> <a id="1932" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1934" href="foundation.universal-quantification.html#1612" class="Bound">l2</a><a id="1936" class="Symbol">)</a>
  <a id="1940" href="foundation.universal-quantification.html#1915" class="Function">for-all</a> <a id="1948" class="Symbol">=</a> <a id="1950" href="foundation.universal-quantification.html#1726" class="Function">type-for-all-Prop</a>

  <a id="1971" href="foundation.universal-quantification.html#1971" class="Function">∀&#39;</a> <a id="1974" class="Symbol">:</a> <a id="1976" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1981" class="Symbol">(</a><a id="1982" href="foundation.universal-quantification.html#1609" class="Bound">l1</a> <a id="1985" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1987" href="foundation.universal-quantification.html#1612" class="Bound">l2</a><a id="1989" class="Symbol">)</a>
  <a id="1993" href="foundation.universal-quantification.html#1971" class="Function">∀&#39;</a> <a id="1996" class="Symbol">=</a> <a id="1998" href="foundation.universal-quantification.html#1665" class="Function">for-all-Prop</a>
</pre>
### The universal property of universal quantification

The
{{#concept "universal property" Disambiguation="of universal quantification" Agda=universal-property-for-all}}
of the universal quantification `∀ (a : A), (P a)` states that for every
proposition `R`, the canonical map

```text
  (∀ (a : A), (R → P a)) → (R → ∀ (a : A), (P a))
```

is a [logical equivalence](foundation.logical-equivalences.md). Indeed, this
holds for any type `R`.

<pre class="Agda"><a id="2469" class="Keyword">module</a> <a id="2476" href="foundation.universal-quantification.html#2476" class="Module">_</a>
  <a id="2480" class="Symbol">{</a><a id="2481" href="foundation.universal-quantification.html#2481" class="Bound">l1</a> <a id="2484" href="foundation.universal-quantification.html#2484" class="Bound">l2</a> <a id="2487" class="Symbol">:</a> <a id="2489" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2494" class="Symbol">}</a> <a id="2496" class="Symbol">(</a><a id="2497" href="foundation.universal-quantification.html#2497" class="Bound">A</a> <a id="2499" class="Symbol">:</a> <a id="2501" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2504" href="foundation.universal-quantification.html#2481" class="Bound">l1</a><a id="2506" class="Symbol">)</a> <a id="2508" class="Symbol">(</a><a id="2509" href="foundation.universal-quantification.html#2509" class="Bound">P</a> <a id="2511" class="Symbol">:</a> <a id="2513" href="foundation.universal-quantification.html#2497" class="Bound">A</a> <a id="2515" class="Symbol">→</a> <a id="2517" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2522" href="foundation.universal-quantification.html#2484" class="Bound">l2</a><a id="2524" class="Symbol">)</a>
  <a id="2528" class="Keyword">where</a>

  <a id="2537" href="foundation.universal-quantification.html#2537" class="Function">universal-property-for-all</a> <a id="2564" class="Symbol">:</a> <a id="2566" class="Symbol">{</a><a id="2567" href="foundation.universal-quantification.html#2567" class="Bound">l3</a> <a id="2570" class="Symbol">:</a> <a id="2572" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2577" class="Symbol">}</a> <a id="2579" class="Symbol">(</a><a id="2580" href="foundation.universal-quantification.html#2580" class="Bound">S</a> <a id="2582" class="Symbol">:</a> <a id="2584" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2589" href="foundation.universal-quantification.html#2567" class="Bound">l3</a><a id="2591" class="Symbol">)</a> <a id="2593" class="Symbol">→</a> <a id="2595" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="2601" href="foundation.universal-quantification.html#2537" class="Function">universal-property-for-all</a> <a id="2628" href="foundation.universal-quantification.html#2628" class="Bound">S</a> <a id="2630" class="Symbol">=</a>
    <a id="2636" class="Symbol">{</a><a id="2637" href="foundation.universal-quantification.html#2637" class="Bound">l</a> <a id="2639" class="Symbol">:</a> <a id="2641" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2646" class="Symbol">}</a> <a id="2648" class="Symbol">(</a><a id="2649" href="foundation.universal-quantification.html#2649" class="Bound">R</a> <a id="2651" class="Symbol">:</a> <a id="2653" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2658" href="foundation.universal-quantification.html#2637" class="Bound">l</a><a id="2659" class="Symbol">)</a> <a id="2661" class="Symbol">→</a>
    <a id="2667" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2677" class="Symbol">((</a><a id="2679" href="foundation.universal-quantification.html#1971" class="Function">∀&#39;</a> <a id="2682" href="foundation.universal-quantification.html#2497" class="Bound">A</a> <a id="2684" class="Symbol">(λ</a> <a id="2687" href="foundation.universal-quantification.html#2687" class="Bound">a</a> <a id="2689" class="Symbol">→</a> <a id="2691" href="foundation.universal-quantification.html#2649" class="Bound">R</a> <a id="2693" href="foundation-core.propositions.html#8926" class="Function Operator">⇒</a> <a id="2695" href="foundation.universal-quantification.html#2509" class="Bound">P</a> <a id="2697" href="foundation.universal-quantification.html#2687" class="Bound">a</a><a id="2698" class="Symbol">))</a> <a id="2701" href="foundation.logical-equivalences.html#2857" class="Function Operator">⇔</a> <a id="2703" class="Symbol">(</a><a id="2704" href="foundation.universal-quantification.html#2649" class="Bound">R</a> <a id="2706" href="foundation-core.propositions.html#8926" class="Function Operator">⇒</a> <a id="2708" href="foundation.universal-quantification.html#2628" class="Bound">S</a><a id="2709" class="Symbol">))</a>

  <a id="2715" href="foundation.universal-quantification.html#2715" class="Function">ev-for-all</a> <a id="2726" class="Symbol">:</a>
    <a id="2732" class="Symbol">{</a><a id="2733" href="foundation.universal-quantification.html#2733" class="Bound">l</a> <a id="2735" class="Symbol">:</a> <a id="2737" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2742" class="Symbol">}</a> <a id="2744" class="Symbol">{</a><a id="2745" href="foundation.universal-quantification.html#2745" class="Bound">B</a> <a id="2747" class="Symbol">:</a> <a id="2749" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2752" href="foundation.universal-quantification.html#2733" class="Bound">l</a><a id="2753" class="Symbol">}</a> <a id="2755" class="Symbol">→</a>
    <a id="2761" href="foundation.universal-quantification.html#1915" class="Function">for-all</a> <a id="2769" href="foundation.universal-quantification.html#2497" class="Bound">A</a> <a id="2771" class="Symbol">(λ</a> <a id="2774" href="foundation.universal-quantification.html#2774" class="Bound">a</a> <a id="2776" class="Symbol">→</a> <a id="2778" href="foundation-core.propositions.html#8326" class="Function">function-Prop</a> <a id="2792" href="foundation.universal-quantification.html#2745" class="Bound">B</a> <a id="2794" class="Symbol">(</a><a id="2795" href="foundation.universal-quantification.html#2509" class="Bound">P</a> <a id="2797" href="foundation.universal-quantification.html#2774" class="Bound">a</a><a id="2798" class="Symbol">))</a> <a id="2801" class="Symbol">→</a> <a id="2803" href="foundation.universal-quantification.html#2745" class="Bound">B</a> <a id="2805" class="Symbol">→</a> <a id="2807" href="foundation.universal-quantification.html#1915" class="Function">for-all</a> <a id="2815" href="foundation.universal-quantification.html#2497" class="Bound">A</a> <a id="2817" href="foundation.universal-quantification.html#2509" class="Bound">P</a>
  <a id="2821" href="foundation.universal-quantification.html#2715" class="Function">ev-for-all</a> <a id="2832" href="foundation.universal-quantification.html#2832" class="Bound">f</a> <a id="2834" href="foundation.universal-quantification.html#2834" class="Bound">r</a> <a id="2836" href="foundation.universal-quantification.html#2836" class="Bound">a</a> <a id="2838" class="Symbol">=</a> <a id="2840" href="foundation.universal-quantification.html#2832" class="Bound">f</a> <a id="2842" href="foundation.universal-quantification.html#2836" class="Bound">a</a> <a id="2844" href="foundation.universal-quantification.html#2834" class="Bound">r</a>
</pre>
## Properties

### Universal quantification satisfies its universal property

<pre class="Agda"><a id="2937" class="Keyword">module</a> <a id="2944" href="foundation.universal-quantification.html#2944" class="Module">_</a>
  <a id="2948" class="Symbol">{</a><a id="2949" href="foundation.universal-quantification.html#2949" class="Bound">l1</a> <a id="2952" href="foundation.universal-quantification.html#2952" class="Bound">l2</a> <a id="2955" class="Symbol">:</a> <a id="2957" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2962" class="Symbol">}</a> <a id="2964" class="Symbol">(</a><a id="2965" href="foundation.universal-quantification.html#2965" class="Bound">A</a> <a id="2967" class="Symbol">:</a> <a id="2969" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2972" href="foundation.universal-quantification.html#2949" class="Bound">l1</a><a id="2974" class="Symbol">)</a> <a id="2976" class="Symbol">(</a><a id="2977" href="foundation.universal-quantification.html#2977" class="Bound">P</a> <a id="2979" class="Symbol">:</a> <a id="2981" href="foundation.universal-quantification.html#2965" class="Bound">A</a> <a id="2983" class="Symbol">→</a> <a id="2985" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2990" href="foundation.universal-quantification.html#2952" class="Bound">l2</a><a id="2992" class="Symbol">)</a>
  <a id="2996" class="Keyword">where</a>

  <a id="3005" href="foundation.universal-quantification.html#3005" class="Function">map-up-for-all</a> <a id="3020" class="Symbol">:</a>
    <a id="3026" class="Symbol">{</a><a id="3027" href="foundation.universal-quantification.html#3027" class="Bound">l</a> <a id="3029" class="Symbol">:</a> <a id="3031" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3036" class="Symbol">}</a> <a id="3038" class="Symbol">{</a><a id="3039" href="foundation.universal-quantification.html#3039" class="Bound">B</a> <a id="3041" class="Symbol">:</a> <a id="3043" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3046" href="foundation.universal-quantification.html#3027" class="Bound">l</a><a id="3047" class="Symbol">}</a> <a id="3049" class="Symbol">→</a>
    <a id="3055" class="Symbol">(</a><a id="3056" href="foundation.universal-quantification.html#3039" class="Bound">B</a> <a id="3058" class="Symbol">→</a> <a id="3060" href="foundation.universal-quantification.html#1915" class="Function">for-all</a> <a id="3068" href="foundation.universal-quantification.html#2965" class="Bound">A</a> <a id="3070" href="foundation.universal-quantification.html#2977" class="Bound">P</a><a id="3071" class="Symbol">)</a> <a id="3073" class="Symbol">→</a> <a id="3075" href="foundation.universal-quantification.html#1915" class="Function">for-all</a> <a id="3083" href="foundation.universal-quantification.html#2965" class="Bound">A</a> <a id="3085" class="Symbol">(λ</a> <a id="3088" href="foundation.universal-quantification.html#3088" class="Bound">a</a> <a id="3090" class="Symbol">→</a> <a id="3092" href="foundation-core.propositions.html#8326" class="Function">function-Prop</a> <a id="3106" href="foundation.universal-quantification.html#3039" class="Bound">B</a> <a id="3108" class="Symbol">(</a><a id="3109" href="foundation.universal-quantification.html#2977" class="Bound">P</a> <a id="3111" href="foundation.universal-quantification.html#3088" class="Bound">a</a><a id="3112" class="Symbol">))</a>
  <a id="3117" href="foundation.universal-quantification.html#3005" class="Function">map-up-for-all</a> <a id="3132" href="foundation.universal-quantification.html#3132" class="Bound">f</a> <a id="3134" href="foundation.universal-quantification.html#3134" class="Bound">a</a> <a id="3136" href="foundation.universal-quantification.html#3136" class="Bound">r</a> <a id="3138" class="Symbol">=</a> <a id="3140" href="foundation.universal-quantification.html#3132" class="Bound">f</a> <a id="3142" href="foundation.universal-quantification.html#3136" class="Bound">r</a> <a id="3144" href="foundation.universal-quantification.html#3134" class="Bound">a</a>

  <a id="3149" href="foundation.universal-quantification.html#3149" class="Function">is-equiv-ev-for-all</a> <a id="3169" class="Symbol">:</a>
    <a id="3175" class="Symbol">{</a><a id="3176" href="foundation.universal-quantification.html#3176" class="Bound">l</a> <a id="3178" class="Symbol">:</a> <a id="3180" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3185" class="Symbol">}</a> <a id="3187" class="Symbol">{</a><a id="3188" href="foundation.universal-quantification.html#3188" class="Bound">B</a> <a id="3190" class="Symbol">:</a> <a id="3192" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3195" href="foundation.universal-quantification.html#3176" class="Bound">l</a><a id="3196" class="Symbol">}</a> <a id="3198" class="Symbol">→</a> <a id="3200" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="3209" class="Symbol">(</a><a id="3210" href="foundation.universal-quantification.html#2715" class="Function">ev-for-all</a> <a id="3221" href="foundation.universal-quantification.html#2965" class="Bound">A</a> <a id="3223" href="foundation.universal-quantification.html#2977" class="Bound">P</a> <a id="3225" class="Symbol">{</a><a id="3226" class="Argument">B</a> <a id="3228" class="Symbol">=</a> <a id="3230" href="foundation.universal-quantification.html#3188" class="Bound">B</a><a id="3231" class="Symbol">})</a>
  <a id="3236" href="foundation.universal-quantification.html#3149" class="Function">is-equiv-ev-for-all</a> <a id="3256" class="Symbol">{</a><a id="3257" class="Argument">B</a> <a id="3259" class="Symbol">=</a> <a id="3261" href="foundation.universal-quantification.html#3261" class="Bound">B</a><a id="3262" class="Symbol">}</a> <a id="3264" class="Symbol">=</a>
    <a id="3270" href="foundation.logical-equivalences.html#4962" class="Function">is-equiv-has-converse</a>
      <a id="3298" class="Symbol">(</a> <a id="3300" href="foundation.universal-quantification.html#1971" class="Function">∀&#39;</a> <a id="3303" href="foundation.universal-quantification.html#2965" class="Bound">A</a> <a id="3305" class="Symbol">(λ</a> <a id="3308" href="foundation.universal-quantification.html#3308" class="Bound">a</a> <a id="3310" class="Symbol">→</a> <a id="3312" href="foundation-core.propositions.html#8326" class="Function">function-Prop</a> <a id="3326" href="foundation.universal-quantification.html#3261" class="Bound">B</a> <a id="3328" class="Symbol">(</a><a id="3329" href="foundation.universal-quantification.html#2977" class="Bound">P</a> <a id="3331" href="foundation.universal-quantification.html#3308" class="Bound">a</a><a id="3332" class="Symbol">)))</a>
      <a id="3342" class="Symbol">(</a> <a id="3344" href="foundation-core.propositions.html#8326" class="Function">function-Prop</a> <a id="3358" href="foundation.universal-quantification.html#3261" class="Bound">B</a> <a id="3360" class="Symbol">(</a><a id="3361" href="foundation.universal-quantification.html#1971" class="Function">∀&#39;</a> <a id="3364" href="foundation.universal-quantification.html#2965" class="Bound">A</a> <a id="3366" href="foundation.universal-quantification.html#2977" class="Bound">P</a><a id="3367" class="Symbol">))</a>
      <a id="3376" class="Symbol">(</a> <a id="3378" href="foundation.universal-quantification.html#3005" class="Function">map-up-for-all</a><a id="3392" class="Symbol">)</a>

  <a id="3397" href="foundation.universal-quantification.html#3397" class="Function">up-for-all</a> <a id="3408" class="Symbol">:</a> <a id="3410" href="foundation.universal-quantification.html#2537" class="Function">universal-property-for-all</a> <a id="3437" href="foundation.universal-quantification.html#2965" class="Bound">A</a> <a id="3439" href="foundation.universal-quantification.html#2977" class="Bound">P</a> <a id="3441" class="Symbol">(</a><a id="3442" href="foundation.universal-quantification.html#1971" class="Function">∀&#39;</a> <a id="3445" href="foundation.universal-quantification.html#2965" class="Bound">A</a> <a id="3447" href="foundation.universal-quantification.html#2977" class="Bound">P</a><a id="3448" class="Symbol">)</a>
  <a id="3452" href="foundation.universal-quantification.html#3397" class="Function">up-for-all</a> <a id="3463" href="foundation.universal-quantification.html#3463" class="Bound">R</a> <a id="3465" class="Symbol">=</a> <a id="3467" class="Symbol">(</a><a id="3468" href="foundation.universal-quantification.html#2715" class="Function">ev-for-all</a> <a id="3479" href="foundation.universal-quantification.html#2965" class="Bound">A</a> <a id="3481" href="foundation.universal-quantification.html#2977" class="Bound">P</a> <a id="3483" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3485" href="foundation.universal-quantification.html#3005" class="Function">map-up-for-all</a><a id="3499" class="Symbol">)</a>
</pre>
## See also

- Universal quantification is the indexed counterpart to
  [conjunction](foundation.conjunction.md).

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External links

- [universal quantifier](https://ncatlab.org/nlab/show/universal+quantifier) at
  $n$Lab
- [Universal quantification](https://en.wikipedia.org/wiki/Universal_quantification)
  at Wikipedia
