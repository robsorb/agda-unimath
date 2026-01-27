# Cauchy sequences in complete metric spaces

<pre class="Agda"><a id="55" class="Symbol">{-#</a> <a id="59" class="Keyword">OPTIONS</a> <a id="67" class="Pragma">--lossy-unification</a> <a id="87" class="Symbol">#-}</a>

<a id="92" class="Keyword">module</a> <a id="99" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html" class="Module">metric-spaces.cauchy-sequences-complete-metric-spaces</a> <a id="153" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="209" class="Keyword">open</a> <a id="214" class="Keyword">import</a> <a id="221" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="253" class="Keyword">open</a> <a id="258" class="Keyword">import</a> <a id="265" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="311" class="Keyword">open</a> <a id="316" class="Keyword">import</a> <a id="323" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="351" class="Keyword">open</a> <a id="356" class="Keyword">import</a> <a id="363" href="metric-spaces.cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.cauchy-approximations-metric-spaces</a>
<a id="413" class="Keyword">open</a> <a id="418" class="Keyword">import</a> <a id="425" href="metric-spaces.cauchy-sequences-metric-spaces.html" class="Module">metric-spaces.cauchy-sequences-metric-spaces</a>
<a id="470" class="Keyword">open</a> <a id="475" class="Keyword">import</a> <a id="482" href="metric-spaces.complete-metric-spaces.html" class="Module">metric-spaces.complete-metric-spaces</a>
<a id="519" class="Keyword">open</a> <a id="524" class="Keyword">import</a> <a id="531" href="metric-spaces.convergent-cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.convergent-cauchy-approximations-metric-spaces</a>
<a id="592" class="Keyword">open</a> <a id="597" class="Keyword">import</a> <a id="604" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
</pre>
</details>

## Idea

A [Cauchy sequence](metric-spaces.cauchy-sequences-metric-spaces.md) in a
[complete metric space](metric-spaces.complete-metric-spaces.md) is a Cauchy
sequence in the underlying [metric space](metric-spaces.metric-spaces.md).
Cauchy sequences in complete metric spaces always have a limit.

## Definition

<pre class="Agda"><a id="972" class="Keyword">module</a> <a id="979" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#979" class="Module">_</a>
  <a id="983" class="Symbol">{</a><a id="984" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#984" class="Bound">l1</a> <a id="987" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#987" class="Bound">l2</a> <a id="990" class="Symbol">:</a> <a id="992" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="997" class="Symbol">}</a> <a id="999" class="Symbol">(</a><a id="1000" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1000" class="Bound">M</a> <a id="1002" class="Symbol">:</a> <a id="1004" href="metric-spaces.complete-metric-spaces.html#1856" class="Function">Complete-Metric-Space</a> <a id="1026" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#984" class="Bound">l1</a> <a id="1029" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#987" class="Bound">l2</a><a id="1031" class="Symbol">)</a>
  <a id="1035" class="Keyword">where</a>

  <a id="1044" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1044" class="Function">cauchy-sequence-Complete-Metric-Space</a> <a id="1082" class="Symbol">:</a> <a id="1084" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1087" class="Symbol">(</a><a id="1088" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#984" class="Bound">l1</a> <a id="1091" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1093" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#987" class="Bound">l2</a><a id="1095" class="Symbol">)</a>
  <a id="1099" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1044" class="Function">cauchy-sequence-Complete-Metric-Space</a> <a id="1137" class="Symbol">=</a>
    <a id="1143" href="metric-spaces.cauchy-sequences-metric-spaces.html#3311" class="Function">cauchy-sequence-Metric-Space</a> <a id="1172" class="Symbol">(</a><a id="1173" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="1208" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1000" class="Bound">M</a><a id="1209" class="Symbol">)</a>

  <a id="1214" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1214" class="Function">is-limit-cauchy-sequence-Complete-Metric-Space</a> <a id="1261" class="Symbol">:</a>
    <a id="1267" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1044" class="Function">cauchy-sequence-Complete-Metric-Space</a> <a id="1305" class="Symbol">→</a> <a id="1307" href="metric-spaces.complete-metric-spaces.html#2179" class="Function">type-Complete-Metric-Space</a> <a id="1334" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1000" class="Bound">M</a> <a id="1336" class="Symbol">→</a> <a id="1338" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1341" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#987" class="Bound">l2</a>
  <a id="1346" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1214" class="Function">is-limit-cauchy-sequence-Complete-Metric-Space</a> <a id="1393" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1393" class="Bound">x</a> <a id="1395" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1395" class="Bound">l</a> <a id="1397" class="Symbol">=</a>
    <a id="1403" href="metric-spaces.cauchy-sequences-metric-spaces.html#5770" class="Function">is-limit-cauchy-sequence-Metric-Space</a>
      <a id="1447" class="Symbol">(</a> <a id="1449" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="1484" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1000" class="Bound">M</a><a id="1485" class="Symbol">)</a>
      <a id="1493" class="Symbol">(</a> <a id="1495" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1393" class="Bound">x</a><a id="1496" class="Symbol">)</a>
      <a id="1504" class="Symbol">(</a> <a id="1506" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1395" class="Bound">l</a><a id="1507" class="Symbol">)</a>
</pre>
## Properties

### Every Cauchy sequence in a complete metric space has a limit

<pre class="Agda"><a id="1603" class="Keyword">module</a> <a id="1610" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1610" class="Module">_</a>
  <a id="1614" class="Symbol">{</a><a id="1615" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1615" class="Bound">l1</a> <a id="1618" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1618" class="Bound">l2</a> <a id="1621" class="Symbol">:</a> <a id="1623" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1628" class="Symbol">}</a> <a id="1630" class="Symbol">(</a><a id="1631" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1631" class="Bound">M</a> <a id="1633" class="Symbol">:</a> <a id="1635" href="metric-spaces.complete-metric-spaces.html#1856" class="Function">Complete-Metric-Space</a> <a id="1657" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1615" class="Bound">l1</a> <a id="1660" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1618" class="Bound">l2</a><a id="1662" class="Symbol">)</a>
  <a id="1666" class="Symbol">(</a><a id="1667" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1667" class="Bound">x</a> <a id="1669" class="Symbol">:</a> <a id="1671" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1044" class="Function">cauchy-sequence-Complete-Metric-Space</a> <a id="1709" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1631" class="Bound">M</a><a id="1710" class="Symbol">)</a>
  <a id="1714" class="Keyword">where</a>

  <a id="1723" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1723" class="Function">limit-cauchy-sequence-Complete-Metric-Space</a> <a id="1767" class="Symbol">:</a> <a id="1769" href="metric-spaces.complete-metric-spaces.html#2179" class="Function">type-Complete-Metric-Space</a> <a id="1796" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1631" class="Bound">M</a>
  <a id="1800" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1723" class="Function">limit-cauchy-sequence-Complete-Metric-Space</a> <a id="1844" class="Symbol">=</a>
    <a id="1850" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>
      <a id="1860" class="Symbol">(</a> <a id="1862" href="metric-spaces.complete-metric-spaces.html#2305" class="Function">is-complete-metric-space-Complete-Metric-Space</a>
        <a id="1917" class="Symbol">(</a> <a id="1919" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1631" class="Bound">M</a><a id="1920" class="Symbol">)</a>
        <a id="1930" class="Symbol">(</a> <a id="1932" href="metric-spaces.cauchy-sequences-metric-spaces.html#9774" class="Function">cauchy-approximation-cauchy-sequence-Metric-Space</a>
          <a id="1992" class="Symbol">(</a> <a id="1994" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="2029" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1631" class="Bound">M</a><a id="2030" class="Symbol">)</a>
          <a id="2042" class="Symbol">(</a> <a id="2044" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1667" class="Bound">x</a><a id="2045" class="Symbol">)))</a>

  <a id="2052" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#2052" class="Function">is-limit-limit-cauchy-sequence-Complete-Metric-Space</a> <a id="2105" class="Symbol">:</a>
    <a id="2111" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1214" class="Function">is-limit-cauchy-sequence-Complete-Metric-Space</a>
      <a id="2164" class="Symbol">(</a> <a id="2166" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1631" class="Bound">M</a><a id="2167" class="Symbol">)</a>
      <a id="2175" class="Symbol">(</a> <a id="2177" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1667" class="Bound">x</a><a id="2178" class="Symbol">)</a>
      <a id="2186" class="Symbol">(</a> <a id="2188" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1723" class="Function">limit-cauchy-sequence-Complete-Metric-Space</a><a id="2231" class="Symbol">)</a>
  <a id="2235" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#2052" class="Function">is-limit-limit-cauchy-sequence-Complete-Metric-Space</a> <a id="2288" class="Symbol">=</a>
    <a id="2294" href="metric-spaces.cauchy-sequences-metric-spaces.html#12530" class="Function">is-limit-cauchy-sequence-limit-cauchy-approximation-cauchy-sequence-Metric-Space</a>
      <a id="2381" class="Symbol">(</a> <a id="2383" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="2418" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1631" class="Bound">M</a><a id="2419" class="Symbol">)</a>
      <a id="2427" class="Symbol">(</a> <a id="2429" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1667" class="Bound">x</a><a id="2430" class="Symbol">)</a>
      <a id="2438" class="Symbol">(</a> <a id="2440" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1723" class="Function">limit-cauchy-sequence-Complete-Metric-Space</a><a id="2483" class="Symbol">)</a>
      <a id="2491" class="Symbol">(</a> <a id="2493" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>
        <a id="2505" class="Symbol">(</a> <a id="2507" href="metric-spaces.complete-metric-spaces.html#2305" class="Function">is-complete-metric-space-Complete-Metric-Space</a>
          <a id="2564" class="Symbol">(</a> <a id="2566" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1631" class="Bound">M</a><a id="2567" class="Symbol">)</a>
          <a id="2579" class="Symbol">(</a> <a id="2581" href="metric-spaces.cauchy-sequences-metric-spaces.html#9774" class="Function">cauchy-approximation-cauchy-sequence-Metric-Space</a>
            <a id="2643" class="Symbol">(</a> <a id="2645" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="2680" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1631" class="Bound">M</a><a id="2681" class="Symbol">)</a>
            <a id="2695" class="Symbol">(</a> <a id="2697" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1667" class="Bound">x</a><a id="2698" class="Symbol">))))</a>

  <a id="2706" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#2706" class="Function">has-limit-cauchy-sequence-Complete-Metric-Space</a> <a id="2754" class="Symbol">:</a>
    <a id="2760" href="metric-spaces.cauchy-sequences-metric-spaces.html#6066" class="Function">has-limit-cauchy-sequence-Metric-Space</a>
      <a id="2805" class="Symbol">(</a> <a id="2807" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="2842" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1631" class="Bound">M</a><a id="2843" class="Symbol">)</a>
      <a id="2851" class="Symbol">(</a> <a id="2853" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1667" class="Bound">x</a><a id="2854" class="Symbol">)</a>
  <a id="2858" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#2706" class="Function">has-limit-cauchy-sequence-Complete-Metric-Space</a> <a id="2906" class="Symbol">=</a>
    <a id="2912" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#1723" class="Function">limit-cauchy-sequence-Complete-Metric-Space</a> <a id="2956" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="2962" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#2052" class="Function">is-limit-limit-cauchy-sequence-Complete-Metric-Space</a>
</pre>
### If every Cauchy sequence has a limit in a metric space, the metric space is complete

<pre class="Agda"><a id="3118" class="Keyword">module</a> <a id="3125" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3125" class="Module">_</a>
  <a id="3129" class="Symbol">{</a><a id="3130" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3130" class="Bound">l1</a> <a id="3133" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3133" class="Bound">l2</a> <a id="3136" class="Symbol">:</a> <a id="3138" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3143" class="Symbol">}</a> <a id="3145" class="Symbol">(</a><a id="3146" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3146" class="Bound">M</a> <a id="3148" class="Symbol">:</a> <a id="3150" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="3163" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3130" class="Bound">l1</a> <a id="3166" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3133" class="Bound">l2</a><a id="3168" class="Symbol">)</a>
  <a id="3172" class="Keyword">where</a>

  <a id="3181" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3181" class="Function">cauchy-sequences-have-limits-Metric-Space</a> <a id="3223" class="Symbol">:</a> <a id="3225" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3228" class="Symbol">(</a><a id="3229" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3130" class="Bound">l1</a> <a id="3232" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3234" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3133" class="Bound">l2</a><a id="3236" class="Symbol">)</a>
  <a id="3240" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3181" class="Function">cauchy-sequences-have-limits-Metric-Space</a> <a id="3282" class="Symbol">=</a>
    <a id="3288" class="Symbol">(</a><a id="3289" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3289" class="Bound">x</a> <a id="3291" class="Symbol">:</a> <a id="3293" href="metric-spaces.cauchy-sequences-metric-spaces.html#3311" class="Function">cauchy-sequence-Metric-Space</a> <a id="3322" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3146" class="Bound">M</a><a id="3323" class="Symbol">)</a> <a id="3325" class="Symbol">→</a>
    <a id="3331" href="metric-spaces.cauchy-sequences-metric-spaces.html#6066" class="Function">has-limit-cauchy-sequence-Metric-Space</a> <a id="3370" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3146" class="Bound">M</a> <a id="3372" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3289" class="Bound">x</a>

<a id="3375" class="Keyword">module</a> <a id="3382" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3382" class="Module">_</a>
  <a id="3386" class="Symbol">{</a><a id="3387" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3387" class="Bound">l1</a> <a id="3390" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3390" class="Bound">l2</a> <a id="3393" class="Symbol">:</a> <a id="3395" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3400" class="Symbol">}</a> <a id="3402" class="Symbol">(</a><a id="3403" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3403" class="Bound">M</a> <a id="3405" class="Symbol">:</a> <a id="3407" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="3420" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3387" class="Bound">l1</a> <a id="3423" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3390" class="Bound">l2</a><a id="3425" class="Symbol">)</a>
  <a id="3429" class="Symbol">(</a><a id="3430" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3430" class="Bound">H</a> <a id="3432" class="Symbol">:</a> <a id="3434" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3181" class="Function">cauchy-sequences-have-limits-Metric-Space</a> <a id="3476" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3403" class="Bound">M</a><a id="3477" class="Symbol">)</a>
  <a id="3481" class="Keyword">where</a>

  <a id="3490" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3490" class="Function">is-complete-metric-space-cauchy-sequences-have-limits-Metric-Space</a> <a id="3557" class="Symbol">:</a>
    <a id="3563" href="metric-spaces.complete-metric-spaces.html#1496" class="Function">is-complete-Metric-Space</a> <a id="3588" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3403" class="Bound">M</a>
  <a id="3592" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3490" class="Function">is-complete-metric-space-cauchy-sequences-have-limits-Metric-Space</a> <a id="3659" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3659" class="Bound">x</a> <a id="3661" class="Symbol">=</a>
    <a id="3667" href="foundation-core.functoriality-dependent-pair-types.html#1778" class="Function">tot</a>
      <a id="3677" class="Symbol">(</a> <a id="3679" href="metric-spaces.cauchy-sequences-metric-spaces.html#20166" class="Function">is-limit-cauchy-approximation-limit-cauchy-sequence-cauchy-approximation-Metric-Space</a>
        <a id="3773" class="Symbol">(</a> <a id="3775" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3403" class="Bound">M</a><a id="3776" class="Symbol">)</a>
        <a id="3786" class="Symbol">(</a> <a id="3788" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3659" class="Bound">x</a><a id="3789" class="Symbol">))</a>
      <a id="3798" class="Symbol">(</a> <a id="3800" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3430" class="Bound">H</a> <a id="3802" class="Symbol">(</a><a id="3803" href="metric-spaces.cauchy-sequences-metric-spaces.html#16181" class="Function">cauchy-sequence-cauchy-approximation-Metric-Space</a> <a id="3853" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3403" class="Bound">M</a> <a id="3855" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3659" class="Bound">x</a><a id="3856" class="Symbol">))</a>

  <a id="3862" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3862" class="Function">complete-metric-space-cauchy-sequences-have-limits-Metric-Space</a> <a id="3926" class="Symbol">:</a>
    <a id="3932" href="metric-spaces.complete-metric-spaces.html#1856" class="Function">Complete-Metric-Space</a> <a id="3954" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3387" class="Bound">l1</a> <a id="3957" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3390" class="Bound">l2</a>
  <a id="3962" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3862" class="Function">complete-metric-space-cauchy-sequences-have-limits-Metric-Space</a> <a id="4026" class="Symbol">=</a>
    <a id="4032" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3403" class="Bound">M</a> <a id="4034" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4036" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html#3490" class="Function">is-complete-metric-space-cauchy-sequences-have-limits-Metric-Space</a>
</pre>