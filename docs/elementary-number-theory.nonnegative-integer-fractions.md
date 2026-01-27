# Nonnegative integer fractions

<pre class="Agda"><a id="42" class="Symbol">{-#</a> <a id="46" class="Keyword">OPTIONS</a> <a id="54" class="Pragma">--lossy-unification</a> <a id="74" class="Symbol">#-}</a>

<a id="79" class="Keyword">module</a> <a id="86" href="elementary-number-theory.nonnegative-integer-fractions.html" class="Module">elementary-number-theory.nonnegative-integer-fractions</a> <a id="141" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="elementary-number-theory.addition-integer-fractions.html" class="Module">elementary-number-theory.addition-integer-fractions</a>
<a id="261" class="Keyword">open</a> <a id="266" class="Keyword">import</a> <a id="273" href="elementary-number-theory.addition-positive-and-negative-integers.html" class="Module">elementary-number-theory.addition-positive-and-negative-integers</a>
<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="elementary-number-theory.integer-fractions.html" class="Module">elementary-number-theory.integer-fractions</a>
<a id="393" class="Keyword">open</a> <a id="398" class="Keyword">import</a> <a id="405" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a>
<a id="439" class="Keyword">open</a> <a id="444" class="Keyword">import</a> <a id="451" href="elementary-number-theory.multiplication-integer-fractions.html" class="Module">elementary-number-theory.multiplication-integer-fractions</a>
<a id="509" class="Keyword">open</a> <a id="514" class="Keyword">import</a> <a id="521" href="elementary-number-theory.multiplication-integers.html" class="Module">elementary-number-theory.multiplication-integers</a>
<a id="570" class="Keyword">open</a> <a id="575" class="Keyword">import</a> <a id="582" href="elementary-number-theory.multiplication-positive-and-negative-integers.html" class="Module">elementary-number-theory.multiplication-positive-and-negative-integers</a>
<a id="653" class="Keyword">open</a> <a id="658" class="Keyword">import</a> <a id="665" href="elementary-number-theory.nonnegative-integers.html" class="Module">elementary-number-theory.nonnegative-integers</a>
<a id="711" class="Keyword">open</a> <a id="716" class="Keyword">import</a> <a id="723" href="elementary-number-theory.positive-and-negative-integers.html" class="Module">elementary-number-theory.positive-and-negative-integers</a>
<a id="779" class="Keyword">open</a> <a id="784" class="Keyword">import</a> <a id="791" href="elementary-number-theory.positive-integer-fractions.html" class="Module">elementary-number-theory.positive-integer-fractions</a>
<a id="843" class="Keyword">open</a> <a id="848" class="Keyword">import</a> <a id="855" href="elementary-number-theory.positive-integers.html" class="Module">elementary-number-theory.positive-integers</a>
<a id="898" class="Keyword">open</a> <a id="903" class="Keyword">import</a> <a id="910" href="elementary-number-theory.reduced-integer-fractions.html" class="Module">elementary-number-theory.reduced-integer-fractions</a>

<a id="962" class="Keyword">open</a> <a id="967" class="Keyword">import</a> <a id="974" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="1006" class="Keyword">open</a> <a id="1011" class="Keyword">import</a> <a id="1018" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="1044" class="Keyword">open</a> <a id="1049" class="Keyword">import</a> <a id="1056" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="1080" class="Keyword">open</a> <a id="1085" class="Keyword">import</a> <a id="1092" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="1112" class="Keyword">open</a> <a id="1117" class="Keyword">import</a> <a id="1124" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="1167" class="Keyword">open</a> <a id="1172" class="Keyword">import</a> <a id="1179" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

An [integer fraction](elementary-number-theory.integer-fractions.md) `x` is said
to be
{{#concept "nonnegative" Disambiguation="integer fraction" Agda=is-nonnegative-fraction-ℤ}}
if its numerator is a
[nonnegative integer](elementary-number-theory.nonnegative-integers.md).

## Definitions

### The property of being a nonnegative integer fraction

<pre class="Agda"><a id="1589" class="Keyword">module</a> <a id="1596" href="elementary-number-theory.nonnegative-integer-fractions.html#1596" class="Module">_</a>
  <a id="1600" class="Symbol">(</a><a id="1601" href="elementary-number-theory.nonnegative-integer-fractions.html#1601" class="Bound">x</a> <a id="1603" class="Symbol">:</a> <a id="1605" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="1615" class="Symbol">)</a>
  <a id="1619" class="Keyword">where</a>

  <a id="1628" href="elementary-number-theory.nonnegative-integer-fractions.html#1628" class="Function">is-nonnegative-fraction-ℤ</a> <a id="1654" class="Symbol">:</a> <a id="1656" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1659" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="1667" href="elementary-number-theory.nonnegative-integer-fractions.html#1628" class="Function">is-nonnegative-fraction-ℤ</a> <a id="1693" class="Symbol">=</a> <a id="1695" href="elementary-number-theory.nonnegative-integers.html#1770" class="Function">is-nonnegative-ℤ</a> <a id="1712" class="Symbol">(</a><a id="1713" href="elementary-number-theory.integer-fractions.html#1422" class="Function">numerator-fraction-ℤ</a> <a id="1734" href="elementary-number-theory.nonnegative-integer-fractions.html#1601" class="Bound">x</a><a id="1735" class="Symbol">)</a>

  <a id="1740" href="elementary-number-theory.nonnegative-integer-fractions.html#1740" class="Function">is-prop-is-nonnegative-fraction-ℤ</a> <a id="1774" class="Symbol">:</a> <a id="1776" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1784" href="elementary-number-theory.nonnegative-integer-fractions.html#1628" class="Function">is-nonnegative-fraction-ℤ</a>
  <a id="1812" href="elementary-number-theory.nonnegative-integer-fractions.html#1740" class="Function">is-prop-is-nonnegative-fraction-ℤ</a> <a id="1846" class="Symbol">=</a>
    <a id="1852" href="elementary-number-theory.nonnegative-integers.html#1868" class="Function">is-prop-is-nonnegative-ℤ</a> <a id="1877" class="Symbol">(</a><a id="1878" href="elementary-number-theory.integer-fractions.html#1422" class="Function">numerator-fraction-ℤ</a> <a id="1899" href="elementary-number-theory.nonnegative-integer-fractions.html#1601" class="Bound">x</a><a id="1900" class="Symbol">)</a>
</pre>
## Properties

### An integer fraction similar to a nonnegative integer fraction is nonnegative

<pre class="Agda"><a id="is-nonnegative-sim-fraction-ℤ"></a><a id="2012" href="elementary-number-theory.nonnegative-integer-fractions.html#2012" class="Function">is-nonnegative-sim-fraction-ℤ</a> <a id="2042" class="Symbol">:</a>
  <a id="2046" class="Symbol">(</a><a id="2047" href="elementary-number-theory.nonnegative-integer-fractions.html#2047" class="Bound">x</a> <a id="2049" href="elementary-number-theory.nonnegative-integer-fractions.html#2049" class="Bound">y</a> <a id="2051" class="Symbol">:</a> <a id="2053" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="2063" class="Symbol">)</a> <a id="2065" class="Symbol">(</a><a id="2066" href="elementary-number-theory.nonnegative-integer-fractions.html#2066" class="Bound">S</a> <a id="2068" class="Symbol">:</a> <a id="2070" href="elementary-number-theory.integer-fractions.html#4242" class="Function">sim-fraction-ℤ</a> <a id="2085" href="elementary-number-theory.nonnegative-integer-fractions.html#2047" class="Bound">x</a> <a id="2087" href="elementary-number-theory.nonnegative-integer-fractions.html#2049" class="Bound">y</a><a id="2088" class="Symbol">)</a> <a id="2090" class="Symbol">→</a>
  <a id="2094" href="elementary-number-theory.nonnegative-integer-fractions.html#1628" class="Function">is-nonnegative-fraction-ℤ</a> <a id="2120" href="elementary-number-theory.nonnegative-integer-fractions.html#2047" class="Bound">x</a> <a id="2122" class="Symbol">→</a>
  <a id="2126" href="elementary-number-theory.nonnegative-integer-fractions.html#1628" class="Function">is-nonnegative-fraction-ℤ</a> <a id="2152" href="elementary-number-theory.nonnegative-integer-fractions.html#2049" class="Bound">y</a>
<a id="2154" href="elementary-number-theory.nonnegative-integer-fractions.html#2012" class="Function">is-nonnegative-sim-fraction-ℤ</a> <a id="2184" href="elementary-number-theory.nonnegative-integer-fractions.html#2184" class="Bound">x</a> <a id="2186" href="elementary-number-theory.nonnegative-integer-fractions.html#2186" class="Bound">y</a> <a id="2188" href="elementary-number-theory.nonnegative-integer-fractions.html#2188" class="Bound">S</a> <a id="2190" href="elementary-number-theory.nonnegative-integer-fractions.html#2190" class="Bound">N</a> <a id="2192" class="Symbol">=</a>
  <a id="2196" href="elementary-number-theory.multiplication-positive-and-negative-integers.html#10458" class="Function">is-nonnegative-left-factor-mul-ℤ</a>
    <a id="2233" class="Symbol">(</a> <a id="2235" href="foundation-core.transport-along-identifications.html#832" class="Function">tr</a>
      <a id="2244" class="Symbol">(</a> <a id="2246" href="elementary-number-theory.nonnegative-integers.html#1770" class="Function">is-nonnegative-ℤ</a><a id="2262" class="Symbol">)</a>
      <a id="2270" class="Symbol">(</a> <a id="2272" href="elementary-number-theory.nonnegative-integer-fractions.html#2188" class="Bound">S</a><a id="2273" class="Symbol">)</a>
      <a id="2281" class="Symbol">(</a> <a id="2283" href="elementary-number-theory.multiplication-positive-and-negative-integers.html#4610" class="Function">is-nonnegative-mul-nonnegative-positive-ℤ</a>
        <a id="2333" class="Symbol">(</a> <a id="2335" href="elementary-number-theory.nonnegative-integer-fractions.html#2190" class="Bound">N</a><a id="2336" class="Symbol">)</a>
        <a id="2346" class="Symbol">(</a> <a id="2348" href="elementary-number-theory.integer-fractions.html#1748" class="Function">is-positive-denominator-fraction-ℤ</a> <a id="2383" href="elementary-number-theory.nonnegative-integer-fractions.html#2186" class="Bound">y</a><a id="2384" class="Symbol">)))</a>
    <a id="2392" class="Symbol">(</a> <a id="2394" href="elementary-number-theory.integer-fractions.html#1748" class="Function">is-positive-denominator-fraction-ℤ</a> <a id="2429" href="elementary-number-theory.nonnegative-integer-fractions.html#2184" class="Bound">x</a><a id="2430" class="Symbol">)</a>
</pre>
### The reduced fraction of a nonnegative integer fraction is nonnegative

<pre class="Agda"><a id="is-nonnegative-reduce-fraction-ℤ"></a><a id="2520" href="elementary-number-theory.nonnegative-integer-fractions.html#2520" class="Function">is-nonnegative-reduce-fraction-ℤ</a> <a id="2553" class="Symbol">:</a>
  <a id="2557" class="Symbol">{</a><a id="2558" href="elementary-number-theory.nonnegative-integer-fractions.html#2558" class="Bound">x</a> <a id="2560" class="Symbol">:</a> <a id="2562" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="2572" class="Symbol">}</a> <a id="2574" class="Symbol">(</a><a id="2575" href="elementary-number-theory.nonnegative-integer-fractions.html#2575" class="Bound">P</a> <a id="2577" class="Symbol">:</a> <a id="2579" href="elementary-number-theory.nonnegative-integer-fractions.html#1628" class="Function">is-nonnegative-fraction-ℤ</a> <a id="2605" href="elementary-number-theory.nonnegative-integer-fractions.html#2558" class="Bound">x</a><a id="2606" class="Symbol">)</a> <a id="2608" class="Symbol">→</a>
  <a id="2612" href="elementary-number-theory.nonnegative-integer-fractions.html#1628" class="Function">is-nonnegative-fraction-ℤ</a> <a id="2638" class="Symbol">(</a><a id="2639" href="elementary-number-theory.reduced-integer-fractions.html#4221" class="Function">reduce-fraction-ℤ</a> <a id="2657" href="elementary-number-theory.nonnegative-integer-fractions.html#2558" class="Bound">x</a><a id="2658" class="Symbol">)</a>
<a id="2660" href="elementary-number-theory.nonnegative-integer-fractions.html#2520" class="Function">is-nonnegative-reduce-fraction-ℤ</a> <a id="2693" class="Symbol">{</a><a id="2694" href="elementary-number-theory.nonnegative-integer-fractions.html#2694" class="Bound">x</a><a id="2695" class="Symbol">}</a> <a id="2697" class="Symbol">=</a>
  <a id="2701" href="elementary-number-theory.nonnegative-integer-fractions.html#2012" class="Function">is-nonnegative-sim-fraction-ℤ</a>
    <a id="2735" class="Symbol">(</a> <a id="2737" href="elementary-number-theory.nonnegative-integer-fractions.html#2694" class="Bound">x</a><a id="2738" class="Symbol">)</a>
    <a id="2744" class="Symbol">(</a> <a id="2746" href="elementary-number-theory.reduced-integer-fractions.html#4221" class="Function">reduce-fraction-ℤ</a> <a id="2764" href="elementary-number-theory.nonnegative-integer-fractions.html#2694" class="Bound">x</a><a id="2765" class="Symbol">)</a>
    <a id="2771" class="Symbol">(</a> <a id="2773" href="elementary-number-theory.reduced-integer-fractions.html#8745" class="Function">sim-reduced-fraction-ℤ</a> <a id="2796" href="elementary-number-theory.nonnegative-integer-fractions.html#2694" class="Bound">x</a><a id="2797" class="Symbol">)</a>
</pre>
### The sum of two nonnegative integer fractions is nonnegative

<pre class="Agda"><a id="is-nonnegative-add-fraction-ℤ"></a><a id="2877" href="elementary-number-theory.nonnegative-integer-fractions.html#2877" class="Function">is-nonnegative-add-fraction-ℤ</a> <a id="2907" class="Symbol">:</a>
  <a id="2911" class="Symbol">{</a><a id="2912" href="elementary-number-theory.nonnegative-integer-fractions.html#2912" class="Bound">x</a> <a id="2914" href="elementary-number-theory.nonnegative-integer-fractions.html#2914" class="Bound">y</a> <a id="2916" class="Symbol">:</a> <a id="2918" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="2928" class="Symbol">}</a> <a id="2930" class="Symbol">→</a>
  <a id="2934" href="elementary-number-theory.nonnegative-integer-fractions.html#1628" class="Function">is-nonnegative-fraction-ℤ</a> <a id="2960" href="elementary-number-theory.nonnegative-integer-fractions.html#2912" class="Bound">x</a> <a id="2962" class="Symbol">→</a>
  <a id="2966" href="elementary-number-theory.nonnegative-integer-fractions.html#1628" class="Function">is-nonnegative-fraction-ℤ</a> <a id="2992" href="elementary-number-theory.nonnegative-integer-fractions.html#2914" class="Bound">y</a> <a id="2994" class="Symbol">→</a>
  <a id="2998" href="elementary-number-theory.nonnegative-integer-fractions.html#1628" class="Function">is-nonnegative-fraction-ℤ</a> <a id="3024" class="Symbol">(</a><a id="3025" href="elementary-number-theory.addition-integer-fractions.html#853" class="Function">add-fraction-ℤ</a> <a id="3040" href="elementary-number-theory.nonnegative-integer-fractions.html#2912" class="Bound">x</a> <a id="3042" href="elementary-number-theory.nonnegative-integer-fractions.html#2914" class="Bound">y</a><a id="3043" class="Symbol">)</a>
<a id="3045" href="elementary-number-theory.nonnegative-integer-fractions.html#2877" class="Function">is-nonnegative-add-fraction-ℤ</a> <a id="3075" class="Symbol">{</a><a id="3076" href="elementary-number-theory.nonnegative-integer-fractions.html#3076" class="Bound">x</a><a id="3077" class="Symbol">}</a> <a id="3079" class="Symbol">{</a><a id="3080" href="elementary-number-theory.nonnegative-integer-fractions.html#3080" class="Bound">y</a><a id="3081" class="Symbol">}</a> <a id="3083" href="elementary-number-theory.nonnegative-integer-fractions.html#3083" class="Bound">P</a> <a id="3085" href="elementary-number-theory.nonnegative-integer-fractions.html#3085" class="Bound">Q</a> <a id="3087" class="Symbol">=</a>
  <a id="3091" href="elementary-number-theory.addition-positive-and-negative-integers.html#3637" class="Function">is-nonnegative-add-ℤ</a>
    <a id="3116" class="Symbol">(</a> <a id="3118" href="elementary-number-theory.multiplication-positive-and-negative-integers.html#4610" class="Function">is-nonnegative-mul-nonnegative-positive-ℤ</a>
      <a id="3166" class="Symbol">(</a> <a id="3168" href="elementary-number-theory.nonnegative-integer-fractions.html#3083" class="Bound">P</a><a id="3169" class="Symbol">)</a>
      <a id="3177" class="Symbol">(</a> <a id="3179" href="elementary-number-theory.integer-fractions.html#1748" class="Function">is-positive-denominator-fraction-ℤ</a> <a id="3214" href="elementary-number-theory.nonnegative-integer-fractions.html#3080" class="Bound">y</a><a id="3215" class="Symbol">))</a>
    <a id="3222" class="Symbol">(</a> <a id="3224" href="elementary-number-theory.multiplication-positive-and-negative-integers.html#4610" class="Function">is-nonnegative-mul-nonnegative-positive-ℤ</a>
      <a id="3272" class="Symbol">(</a> <a id="3274" href="elementary-number-theory.nonnegative-integer-fractions.html#3085" class="Bound">Q</a><a id="3275" class="Symbol">)</a>
      <a id="3283" class="Symbol">(</a> <a id="3285" href="elementary-number-theory.integer-fractions.html#1748" class="Function">is-positive-denominator-fraction-ℤ</a> <a id="3320" href="elementary-number-theory.nonnegative-integer-fractions.html#3076" class="Bound">x</a><a id="3321" class="Symbol">))</a>
</pre>
### The product of two nonnegative integer fractions is nonnegative

<pre class="Agda"><a id="is-nonnegative-mul-nonnegative-fraction-ℤ"></a><a id="3406" href="elementary-number-theory.nonnegative-integer-fractions.html#3406" class="Function">is-nonnegative-mul-nonnegative-fraction-ℤ</a> <a id="3448" class="Symbol">:</a>
  <a id="3452" class="Symbol">{</a><a id="3453" href="elementary-number-theory.nonnegative-integer-fractions.html#3453" class="Bound">x</a> <a id="3455" href="elementary-number-theory.nonnegative-integer-fractions.html#3455" class="Bound">y</a> <a id="3457" class="Symbol">:</a> <a id="3459" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="3469" class="Symbol">}</a> <a id="3471" class="Symbol">→</a>
  <a id="3475" href="elementary-number-theory.nonnegative-integer-fractions.html#1628" class="Function">is-nonnegative-fraction-ℤ</a> <a id="3501" href="elementary-number-theory.nonnegative-integer-fractions.html#3453" class="Bound">x</a> <a id="3503" class="Symbol">→</a>
  <a id="3507" href="elementary-number-theory.nonnegative-integer-fractions.html#1628" class="Function">is-nonnegative-fraction-ℤ</a> <a id="3533" href="elementary-number-theory.nonnegative-integer-fractions.html#3455" class="Bound">y</a> <a id="3535" class="Symbol">→</a>
  <a id="3539" href="elementary-number-theory.nonnegative-integer-fractions.html#1628" class="Function">is-nonnegative-fraction-ℤ</a> <a id="3565" class="Symbol">(</a><a id="3566" href="elementary-number-theory.multiplication-integer-fractions.html#1310" class="Function">mul-fraction-ℤ</a> <a id="3581" href="elementary-number-theory.nonnegative-integer-fractions.html#3453" class="Bound">x</a> <a id="3583" href="elementary-number-theory.nonnegative-integer-fractions.html#3455" class="Bound">y</a><a id="3584" class="Symbol">)</a>
<a id="3586" href="elementary-number-theory.nonnegative-integer-fractions.html#3406" class="Function">is-nonnegative-mul-nonnegative-fraction-ℤ</a> <a id="3628" class="Symbol">=</a> <a id="3630" href="elementary-number-theory.multiplication-positive-and-negative-integers.html#4966" class="Function">is-nonnegative-mul-ℤ</a>
</pre>