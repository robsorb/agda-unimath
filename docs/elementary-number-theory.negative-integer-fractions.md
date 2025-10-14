# Negative integer fractions

<pre class="Agda"><a id="39" class="Symbol">{-#</a> <a id="43" class="Keyword">OPTIONS</a> <a id="51" class="Pragma">--lossy-unification</a> <a id="71" class="Symbol">#-}</a>

<a id="76" class="Keyword">module</a> <a id="83" href="elementary-number-theory.negative-integer-fractions.html" class="Module">elementary-number-theory.negative-integer-fractions</a> <a id="135" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="191" class="Keyword">open</a> <a id="196" class="Keyword">import</a> <a id="203" href="elementary-number-theory.addition-integer-fractions.html" class="Module">elementary-number-theory.addition-integer-fractions</a>
<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="elementary-number-theory.addition-positive-and-negative-integers.html" class="Module">elementary-number-theory.addition-positive-and-negative-integers</a>
<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="elementary-number-theory.integer-fractions.html" class="Module">elementary-number-theory.integer-fractions</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a>
<a id="433" class="Keyword">open</a> <a id="438" class="Keyword">import</a> <a id="445" href="elementary-number-theory.multiplication-integer-fractions.html" class="Module">elementary-number-theory.multiplication-integer-fractions</a>
<a id="503" class="Keyword">open</a> <a id="508" class="Keyword">import</a> <a id="515" href="elementary-number-theory.multiplication-integers.html" class="Module">elementary-number-theory.multiplication-integers</a>
<a id="564" class="Keyword">open</a> <a id="569" class="Keyword">import</a> <a id="576" href="elementary-number-theory.multiplication-positive-and-negative-integers.html" class="Module">elementary-number-theory.multiplication-positive-and-negative-integers</a>
<a id="647" class="Keyword">open</a> <a id="652" class="Keyword">import</a> <a id="659" href="elementary-number-theory.negative-integers.html" class="Module">elementary-number-theory.negative-integers</a>
<a id="702" class="Keyword">open</a> <a id="707" class="Keyword">import</a> <a id="714" href="elementary-number-theory.positive-and-negative-integers.html" class="Module">elementary-number-theory.positive-and-negative-integers</a>
<a id="770" class="Keyword">open</a> <a id="775" class="Keyword">import</a> <a id="782" href="elementary-number-theory.positive-integer-fractions.html" class="Module">elementary-number-theory.positive-integer-fractions</a>
<a id="834" class="Keyword">open</a> <a id="839" class="Keyword">import</a> <a id="846" href="elementary-number-theory.positive-integers.html" class="Module">elementary-number-theory.positive-integers</a>
<a id="889" class="Keyword">open</a> <a id="894" class="Keyword">import</a> <a id="901" href="elementary-number-theory.reduced-integer-fractions.html" class="Module">elementary-number-theory.reduced-integer-fractions</a>

<a id="953" class="Keyword">open</a> <a id="958" class="Keyword">import</a> <a id="965" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="991" class="Keyword">open</a> <a id="996" class="Keyword">import</a> <a id="1003" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="1027" class="Keyword">open</a> <a id="1032" class="Keyword">import</a> <a id="1039" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="1059" class="Keyword">open</a> <a id="1064" class="Keyword">import</a> <a id="1071" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="1114" class="Keyword">open</a> <a id="1119" class="Keyword">import</a> <a id="1126" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

An [integer fraction](elementary-number-theory.integer-fractions.md) `x` is said
to be
{{#concept "negative" Disambiguation="integer fraction" Agda=is-negative-fraction-ℤ}}
if its numerator is a
[negative integer](elementary-number-theory.negative-integers.md).

## Definitions

### The property of being a negative integer fraction

<pre class="Agda"><a id="1521" class="Keyword">module</a> <a id="1528" href="elementary-number-theory.negative-integer-fractions.html#1528" class="Module">_</a>
  <a id="1532" class="Symbol">(</a><a id="1533" href="elementary-number-theory.negative-integer-fractions.html#1533" class="Bound">x</a> <a id="1535" class="Symbol">:</a> <a id="1537" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="1547" class="Symbol">)</a>
  <a id="1551" class="Keyword">where</a>

  <a id="1560" href="elementary-number-theory.negative-integer-fractions.html#1560" class="Function">is-negative-fraction-ℤ</a> <a id="1583" class="Symbol">:</a> <a id="1585" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1588" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="1596" href="elementary-number-theory.negative-integer-fractions.html#1560" class="Function">is-negative-fraction-ℤ</a> <a id="1619" class="Symbol">=</a> <a id="1621" href="elementary-number-theory.negative-integers.html#1776" class="Function">is-negative-ℤ</a> <a id="1635" class="Symbol">(</a><a id="1636" href="elementary-number-theory.integer-fractions.html#1422" class="Function">numerator-fraction-ℤ</a> <a id="1657" href="elementary-number-theory.negative-integer-fractions.html#1533" class="Bound">x</a><a id="1658" class="Symbol">)</a>

  <a id="1663" href="elementary-number-theory.negative-integer-fractions.html#1663" class="Function">is-prop-is-negative-fraction-ℤ</a> <a id="1694" class="Symbol">:</a> <a id="1696" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1704" href="elementary-number-theory.negative-integer-fractions.html#1560" class="Function">is-negative-fraction-ℤ</a>
  <a id="1729" href="elementary-number-theory.negative-integer-fractions.html#1663" class="Function">is-prop-is-negative-fraction-ℤ</a> <a id="1760" class="Symbol">=</a>
    <a id="1766" href="elementary-number-theory.negative-integers.html#1865" class="Function">is-prop-is-negative-ℤ</a> <a id="1788" class="Symbol">(</a><a id="1789" href="elementary-number-theory.integer-fractions.html#1422" class="Function">numerator-fraction-ℤ</a> <a id="1810" href="elementary-number-theory.negative-integer-fractions.html#1533" class="Bound">x</a><a id="1811" class="Symbol">)</a>
</pre>
## Properties

### The negative of a positive integer fraction is negative

<pre class="Agda"><a id="1902" class="Keyword">abstract</a>
  <a id="is-negative-neg-positive-fraction-ℤ"></a><a id="1913" href="elementary-number-theory.negative-integer-fractions.html#1913" class="Function">is-negative-neg-positive-fraction-ℤ</a> <a id="1949" class="Symbol">:</a>
    <a id="1955" class="Symbol">(</a><a id="1956" href="elementary-number-theory.negative-integer-fractions.html#1956" class="Bound">x</a> <a id="1958" class="Symbol">:</a> <a id="1960" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="1970" class="Symbol">)</a> <a id="1972" class="Symbol">→</a> <a id="1974" href="elementary-number-theory.positive-integer-fractions.html#1224" class="Function">is-positive-fraction-ℤ</a> <a id="1997" href="elementary-number-theory.negative-integer-fractions.html#1956" class="Bound">x</a> <a id="1999" class="Symbol">→</a>
    <a id="2005" href="elementary-number-theory.negative-integer-fractions.html#1560" class="Function">is-negative-fraction-ℤ</a> <a id="2028" class="Symbol">(</a><a id="2029" href="elementary-number-theory.integer-fractions.html#2748" class="Function">neg-fraction-ℤ</a> <a id="2044" href="elementary-number-theory.negative-integer-fractions.html#1956" class="Bound">x</a><a id="2045" class="Symbol">)</a>
  <a id="2049" href="elementary-number-theory.negative-integer-fractions.html#1913" class="Function">is-negative-neg-positive-fraction-ℤ</a> <a id="2085" class="Symbol">_</a> <a id="2087" class="Symbol">=</a> <a id="2089" href="elementary-number-theory.positive-and-negative-integers.html#6127" class="Function">is-negative-neg-is-positive-ℤ</a>
</pre>
### The negative of a negative integer fraction is positive

<pre class="Agda"><a id="2193" class="Keyword">abstract</a>
  <a id="is-positive-neg-negative-fraction-ℤ"></a><a id="2204" href="elementary-number-theory.negative-integer-fractions.html#2204" class="Function">is-positive-neg-negative-fraction-ℤ</a> <a id="2240" class="Symbol">:</a>
    <a id="2246" class="Symbol">(</a><a id="2247" href="elementary-number-theory.negative-integer-fractions.html#2247" class="Bound">x</a> <a id="2249" class="Symbol">:</a> <a id="2251" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="2261" class="Symbol">)</a> <a id="2263" class="Symbol">→</a> <a id="2265" href="elementary-number-theory.negative-integer-fractions.html#1560" class="Function">is-negative-fraction-ℤ</a> <a id="2288" href="elementary-number-theory.negative-integer-fractions.html#2247" class="Bound">x</a> <a id="2290" class="Symbol">→</a>
    <a id="2296" href="elementary-number-theory.positive-integer-fractions.html#1224" class="Function">is-positive-fraction-ℤ</a> <a id="2319" class="Symbol">(</a><a id="2320" href="elementary-number-theory.integer-fractions.html#2748" class="Function">neg-fraction-ℤ</a> <a id="2335" href="elementary-number-theory.negative-integer-fractions.html#2247" class="Bound">x</a><a id="2336" class="Symbol">)</a>
  <a id="2340" href="elementary-number-theory.negative-integer-fractions.html#2204" class="Function">is-positive-neg-negative-fraction-ℤ</a> <a id="2376" class="Symbol">_</a> <a id="2378" class="Symbol">=</a> <a id="2380" href="elementary-number-theory.positive-and-negative-integers.html#6440" class="Function">is-positive-neg-is-negative-ℤ</a>
</pre>
### An integer fraction similar to a negative integer fraction is negative

<pre class="Agda"><a id="is-negative-sim-fraction-ℤ"></a><a id="2499" href="elementary-number-theory.negative-integer-fractions.html#2499" class="Function">is-negative-sim-fraction-ℤ</a> <a id="2526" class="Symbol">:</a>
  <a id="2530" class="Symbol">(</a><a id="2531" href="elementary-number-theory.negative-integer-fractions.html#2531" class="Bound">x</a> <a id="2533" href="elementary-number-theory.negative-integer-fractions.html#2533" class="Bound">y</a> <a id="2535" class="Symbol">:</a> <a id="2537" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="2547" class="Symbol">)</a> <a id="2549" class="Symbol">(</a><a id="2550" href="elementary-number-theory.negative-integer-fractions.html#2550" class="Bound">S</a> <a id="2552" class="Symbol">:</a> <a id="2554" href="elementary-number-theory.integer-fractions.html#4242" class="Function">sim-fraction-ℤ</a> <a id="2569" href="elementary-number-theory.negative-integer-fractions.html#2531" class="Bound">x</a> <a id="2571" href="elementary-number-theory.negative-integer-fractions.html#2533" class="Bound">y</a><a id="2572" class="Symbol">)</a> <a id="2574" class="Symbol">→</a>
  <a id="2578" href="elementary-number-theory.negative-integer-fractions.html#1560" class="Function">is-negative-fraction-ℤ</a> <a id="2601" href="elementary-number-theory.negative-integer-fractions.html#2531" class="Bound">x</a> <a id="2603" class="Symbol">→</a>
  <a id="2607" href="elementary-number-theory.negative-integer-fractions.html#1560" class="Function">is-negative-fraction-ℤ</a> <a id="2630" href="elementary-number-theory.negative-integer-fractions.html#2533" class="Bound">y</a>
<a id="2632" href="elementary-number-theory.negative-integer-fractions.html#2499" class="Function">is-negative-sim-fraction-ℤ</a> <a id="2659" href="elementary-number-theory.negative-integer-fractions.html#2659" class="Bound">x</a> <a id="2661" href="elementary-number-theory.negative-integer-fractions.html#2661" class="Bound">y</a> <a id="2663" href="elementary-number-theory.negative-integer-fractions.html#2663" class="Bound">S</a> <a id="2665" href="elementary-number-theory.negative-integer-fractions.html#2665" class="Bound">N</a> <a id="2667" class="Symbol">=</a>
  <a id="2671" href="elementary-number-theory.multiplication-positive-and-negative-integers.html#11805" class="Function">is-negative-right-factor-mul-positive-ℤ</a>
    <a id="2715" class="Symbol">(</a> <a id="2717" href="elementary-number-theory.negative-integers.html#2190" class="Function">is-negative-eq-ℤ</a>
      <a id="2740" class="Symbol">(</a> <a id="2742" href="elementary-number-theory.negative-integer-fractions.html#2663" class="Bound">S</a> <a id="2744" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
        <a id="2754" href="elementary-number-theory.multiplication-integers.html#12689" class="Function">commutative-mul-ℤ</a> <a id="2772" class="Symbol">(</a><a id="2773" href="elementary-number-theory.integer-fractions.html#1422" class="Function">numerator-fraction-ℤ</a> <a id="2794" href="elementary-number-theory.negative-integer-fractions.html#2661" class="Bound">y</a><a id="2795" class="Symbol">)</a> <a id="2797" class="Symbol">(</a><a id="2798" href="elementary-number-theory.integer-fractions.html#1640" class="Function">denominator-fraction-ℤ</a> <a id="2821" href="elementary-number-theory.negative-integer-fractions.html#2659" class="Bound">x</a><a id="2822" class="Symbol">))</a>
      <a id="2831" class="Symbol">(</a> <a id="2833" href="elementary-number-theory.multiplication-positive-and-negative-integers.html#6512" class="Function">is-negative-mul-negative-positive-ℤ</a>
        <a id="2877" class="Symbol">(</a> <a id="2879" href="elementary-number-theory.negative-integer-fractions.html#2665" class="Bound">N</a><a id="2880" class="Symbol">)</a>
        <a id="2890" class="Symbol">(</a> <a id="2892" href="elementary-number-theory.integer-fractions.html#1748" class="Function">is-positive-denominator-fraction-ℤ</a> <a id="2927" href="elementary-number-theory.negative-integer-fractions.html#2661" class="Bound">y</a><a id="2928" class="Symbol">)))</a>
    <a id="2936" class="Symbol">(</a> <a id="2938" href="elementary-number-theory.integer-fractions.html#1748" class="Function">is-positive-denominator-fraction-ℤ</a> <a id="2973" href="elementary-number-theory.negative-integer-fractions.html#2659" class="Bound">x</a><a id="2974" class="Symbol">)</a>
</pre>
### The reduced fraction of a negative integer fraction is negative

<pre class="Agda"><a id="is-negative-reduce-fraction-ℤ"></a><a id="3058" href="elementary-number-theory.negative-integer-fractions.html#3058" class="Function">is-negative-reduce-fraction-ℤ</a> <a id="3088" class="Symbol">:</a>
  <a id="3092" class="Symbol">{</a><a id="3093" href="elementary-number-theory.negative-integer-fractions.html#3093" class="Bound">x</a> <a id="3095" class="Symbol">:</a> <a id="3097" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="3107" class="Symbol">}</a> <a id="3109" class="Symbol">(</a><a id="3110" href="elementary-number-theory.negative-integer-fractions.html#3110" class="Bound">P</a> <a id="3112" class="Symbol">:</a> <a id="3114" href="elementary-number-theory.negative-integer-fractions.html#1560" class="Function">is-negative-fraction-ℤ</a> <a id="3137" href="elementary-number-theory.negative-integer-fractions.html#3093" class="Bound">x</a><a id="3138" class="Symbol">)</a> <a id="3140" class="Symbol">→</a>
  <a id="3144" href="elementary-number-theory.negative-integer-fractions.html#1560" class="Function">is-negative-fraction-ℤ</a> <a id="3167" class="Symbol">(</a><a id="3168" href="elementary-number-theory.reduced-integer-fractions.html#4221" class="Function">reduce-fraction-ℤ</a> <a id="3186" href="elementary-number-theory.negative-integer-fractions.html#3093" class="Bound">x</a><a id="3187" class="Symbol">)</a>
<a id="3189" href="elementary-number-theory.negative-integer-fractions.html#3058" class="Function">is-negative-reduce-fraction-ℤ</a> <a id="3219" class="Symbol">{</a><a id="3220" href="elementary-number-theory.negative-integer-fractions.html#3220" class="Bound">x</a><a id="3221" class="Symbol">}</a> <a id="3223" class="Symbol">=</a>
  <a id="3227" href="elementary-number-theory.negative-integer-fractions.html#2499" class="Function">is-negative-sim-fraction-ℤ</a>
    <a id="3258" class="Symbol">(</a> <a id="3260" href="elementary-number-theory.negative-integer-fractions.html#3220" class="Bound">x</a><a id="3261" class="Symbol">)</a>
    <a id="3267" class="Symbol">(</a> <a id="3269" href="elementary-number-theory.reduced-integer-fractions.html#4221" class="Function">reduce-fraction-ℤ</a> <a id="3287" href="elementary-number-theory.negative-integer-fractions.html#3220" class="Bound">x</a><a id="3288" class="Symbol">)</a>
    <a id="3294" class="Symbol">(</a> <a id="3296" href="elementary-number-theory.reduced-integer-fractions.html#8745" class="Function">sim-reduced-fraction-ℤ</a> <a id="3319" href="elementary-number-theory.negative-integer-fractions.html#3220" class="Bound">x</a><a id="3320" class="Symbol">)</a>
</pre>
### The sum of two negative integer fractions is negative

<pre class="Agda"><a id="is-negative-add-fraction-ℤ"></a><a id="3394" href="elementary-number-theory.negative-integer-fractions.html#3394" class="Function">is-negative-add-fraction-ℤ</a> <a id="3421" class="Symbol">:</a>
  <a id="3425" class="Symbol">{</a><a id="3426" href="elementary-number-theory.negative-integer-fractions.html#3426" class="Bound">x</a> <a id="3428" href="elementary-number-theory.negative-integer-fractions.html#3428" class="Bound">y</a> <a id="3430" class="Symbol">:</a> <a id="3432" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="3442" class="Symbol">}</a> <a id="3444" class="Symbol">→</a>
  <a id="3448" href="elementary-number-theory.negative-integer-fractions.html#1560" class="Function">is-negative-fraction-ℤ</a> <a id="3471" href="elementary-number-theory.negative-integer-fractions.html#3426" class="Bound">x</a> <a id="3473" class="Symbol">→</a>
  <a id="3477" href="elementary-number-theory.negative-integer-fractions.html#1560" class="Function">is-negative-fraction-ℤ</a> <a id="3500" href="elementary-number-theory.negative-integer-fractions.html#3428" class="Bound">y</a> <a id="3502" class="Symbol">→</a>
  <a id="3506" href="elementary-number-theory.negative-integer-fractions.html#1560" class="Function">is-negative-fraction-ℤ</a> <a id="3529" class="Symbol">(</a><a id="3530" href="elementary-number-theory.addition-integer-fractions.html#853" class="Function">add-fraction-ℤ</a> <a id="3545" href="elementary-number-theory.negative-integer-fractions.html#3426" class="Bound">x</a> <a id="3547" href="elementary-number-theory.negative-integer-fractions.html#3428" class="Bound">y</a><a id="3548" class="Symbol">)</a>
<a id="3550" href="elementary-number-theory.negative-integer-fractions.html#3394" class="Function">is-negative-add-fraction-ℤ</a> <a id="3577" class="Symbol">{</a><a id="3578" href="elementary-number-theory.negative-integer-fractions.html#3578" class="Bound">x</a><a id="3579" class="Symbol">}</a> <a id="3581" class="Symbol">{</a><a id="3582" href="elementary-number-theory.negative-integer-fractions.html#3582" class="Bound">y</a><a id="3583" class="Symbol">}</a> <a id="3585" href="elementary-number-theory.negative-integer-fractions.html#3585" class="Bound">P</a> <a id="3587" href="elementary-number-theory.negative-integer-fractions.html#3587" class="Bound">Q</a> <a id="3589" class="Symbol">=</a>
  <a id="3593" href="elementary-number-theory.addition-positive-and-negative-integers.html#4114" class="Function">is-negative-add-ℤ</a>
    <a id="3615" class="Symbol">(</a> <a id="3617" href="elementary-number-theory.multiplication-positive-and-negative-integers.html#6512" class="Function">is-negative-mul-negative-positive-ℤ</a>
      <a id="3659" class="Symbol">(</a> <a id="3661" href="elementary-number-theory.negative-integer-fractions.html#3585" class="Bound">P</a><a id="3662" class="Symbol">)</a>
      <a id="3670" class="Symbol">(</a> <a id="3672" href="elementary-number-theory.integer-fractions.html#1748" class="Function">is-positive-denominator-fraction-ℤ</a> <a id="3707" href="elementary-number-theory.negative-integer-fractions.html#3582" class="Bound">y</a><a id="3708" class="Symbol">))</a>
    <a id="3715" class="Symbol">(</a> <a id="3717" href="elementary-number-theory.multiplication-positive-and-negative-integers.html#6512" class="Function">is-negative-mul-negative-positive-ℤ</a>
      <a id="3759" class="Symbol">(</a> <a id="3761" href="elementary-number-theory.negative-integer-fractions.html#3587" class="Bound">Q</a><a id="3762" class="Symbol">)</a>
      <a id="3770" class="Symbol">(</a> <a id="3772" href="elementary-number-theory.integer-fractions.html#1748" class="Function">is-positive-denominator-fraction-ℤ</a> <a id="3807" href="elementary-number-theory.negative-integer-fractions.html#3578" class="Bound">x</a><a id="3808" class="Symbol">))</a>
</pre>
### The product of two negative integer fractions is positive

<pre class="Agda"><a id="is-positive-mul-negative-fraction-ℤ"></a><a id="3887" href="elementary-number-theory.negative-integer-fractions.html#3887" class="Function">is-positive-mul-negative-fraction-ℤ</a> <a id="3923" class="Symbol">:</a>
  <a id="3927" class="Symbol">{</a><a id="3928" href="elementary-number-theory.negative-integer-fractions.html#3928" class="Bound">x</a> <a id="3930" href="elementary-number-theory.negative-integer-fractions.html#3930" class="Bound">y</a> <a id="3932" class="Symbol">:</a> <a id="3934" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="3944" class="Symbol">}</a> <a id="3946" class="Symbol">→</a>
  <a id="3950" href="elementary-number-theory.negative-integer-fractions.html#1560" class="Function">is-negative-fraction-ℤ</a> <a id="3973" href="elementary-number-theory.negative-integer-fractions.html#3928" class="Bound">x</a> <a id="3975" class="Symbol">→</a>
  <a id="3979" href="elementary-number-theory.negative-integer-fractions.html#1560" class="Function">is-negative-fraction-ℤ</a> <a id="4002" href="elementary-number-theory.negative-integer-fractions.html#3930" class="Bound">y</a> <a id="4004" class="Symbol">→</a>
  <a id="4008" href="elementary-number-theory.positive-integer-fractions.html#1224" class="Function">is-positive-fraction-ℤ</a> <a id="4031" class="Symbol">(</a><a id="4032" href="elementary-number-theory.multiplication-integer-fractions.html#1310" class="Function">mul-fraction-ℤ</a> <a id="4047" href="elementary-number-theory.negative-integer-fractions.html#3928" class="Bound">x</a> <a id="4049" href="elementary-number-theory.negative-integer-fractions.html#3930" class="Bound">y</a><a id="4050" class="Symbol">)</a>
<a id="4052" href="elementary-number-theory.negative-integer-fractions.html#3887" class="Function">is-positive-mul-negative-fraction-ℤ</a> <a id="4088" class="Symbol">=</a> <a id="4090" href="elementary-number-theory.multiplication-positive-and-negative-integers.html#7203" class="Function">is-positive-mul-negative-ℤ</a>
</pre>