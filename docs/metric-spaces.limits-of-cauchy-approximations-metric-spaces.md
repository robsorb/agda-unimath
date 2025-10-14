# Limits of Cauchy approximations in metric spaces

<pre class="Agda"><a id="61" class="Keyword">module</a> <a id="68" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.limits-of-cauchy-approximations-metric-spaces</a> <a id="128" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="184" class="Keyword">open</a> <a id="189" class="Keyword">import</a> <a id="196" href="elementary-number-theory.positive-rational-numbers.html" class="Module">elementary-number-theory.positive-rational-numbers</a>

<a id="248" class="Keyword">open</a> <a id="253" class="Keyword">import</a> <a id="260" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="292" class="Keyword">open</a> <a id="297" class="Keyword">import</a> <a id="304" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="330" class="Keyword">open</a> <a id="335" class="Keyword">import</a> <a id="342" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="368" class="Keyword">open</a> <a id="373" class="Keyword">import</a> <a id="380" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="404" class="Keyword">open</a> <a id="409" class="Keyword">import</a> <a id="416" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="436" class="Keyword">open</a> <a id="441" class="Keyword">import</a> <a id="448" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="491" class="Keyword">open</a> <a id="496" class="Keyword">import</a> <a id="503" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="531" class="Keyword">open</a> <a id="536" class="Keyword">import</a> <a id="543" href="metric-spaces.cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.cauchy-approximations-metric-spaces</a>
<a id="593" class="Keyword">open</a> <a id="598" class="Keyword">import</a> <a id="605" href="metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces.html" class="Module">metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces</a>
<a id="671" class="Keyword">open</a> <a id="676" class="Keyword">import</a> <a id="683" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
</pre>
</details>

## Idea

A [Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md)
`f : ℚ⁺ → A` in a [metric space](metric-spaces.metric-spaces.md) `A` has a
{{#concept "limit" Disambiguation="of a Cauchy approximation in a metric space" Agda=is-limit-cauchy-approximation-Metric-Space}}
`x : A` if `f ε` is near `x` for small `ε : ℚ⁺`. More precisely, `f` has a limit
if `f ε` is in a
`ε + δ`-[neighborhood](metric-spaces.rational-neighborhood-relations.md) of `x`
for all
[positive rationals](elementary-number-theory.positive-rational-numbers.md) `ε`
and `δ`.

These are
[limits](metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces.md)
in the underlying [pseudometric space](metric-spaces.pseudometric-spaces.md)
but, because metric spaces are
[extensional](metric-spaces.extensionality-pseudometric-spaces.md), all limits
of a Cauchy approximation in a metric space are equal.

## Definitions

### The property of having a limit in a metric space

<pre class="Agda"><a id="1707" class="Keyword">module</a> <a id="1714" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1714" class="Module">_</a>
  <a id="1718" class="Symbol">{</a><a id="1719" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1719" class="Bound">l1</a> <a id="1722" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1722" class="Bound">l2</a> <a id="1725" class="Symbol">:</a> <a id="1727" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1732" class="Symbol">}</a> <a id="1734" class="Symbol">(</a><a id="1735" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1735" class="Bound">A</a> <a id="1737" class="Symbol">:</a> <a id="1739" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1752" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1719" class="Bound">l1</a> <a id="1755" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1722" class="Bound">l2</a><a id="1757" class="Symbol">)</a>
  <a id="1761" class="Symbol">(</a><a id="1762" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1762" class="Bound">f</a> <a id="1764" class="Symbol">:</a> <a id="1766" href="metric-spaces.cauchy-approximations-metric-spaces.html#1957" class="Function">cauchy-approximation-Metric-Space</a> <a id="1800" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1735" class="Bound">A</a><a id="1801" class="Symbol">)</a>
  <a id="1805" class="Keyword">where</a>

  <a id="1814" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1814" class="Function">is-limit-cauchy-approximation-prop-Metric-Space</a> <a id="1862" class="Symbol">:</a>
    <a id="1868" href="metric-spaces.metric-spaces.html#5090" class="Function">type-Metric-Space</a> <a id="1886" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1735" class="Bound">A</a> <a id="1888" class="Symbol">→</a> <a id="1890" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1895" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1722" class="Bound">l2</a>
  <a id="1900" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1814" class="Function">is-limit-cauchy-approximation-prop-Metric-Space</a> <a id="1948" class="Symbol">=</a>
    <a id="1954" href="metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces.html#1452" class="Function">is-limit-cauchy-approximation-prop-Pseudometric-Space</a>
      <a id="2014" class="Symbol">(</a> <a id="2016" href="metric-spaces.metric-spaces.html#4998" class="Function">pseudometric-Metric-Space</a> <a id="2042" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1735" class="Bound">A</a><a id="2043" class="Symbol">)</a>
      <a id="2051" class="Symbol">(</a> <a id="2053" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1762" class="Bound">f</a><a id="2054" class="Symbol">)</a>

  <a id="2059" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2059" class="Function">is-limit-cauchy-approximation-Metric-Space</a> <a id="2102" class="Symbol">:</a>
    <a id="2108" href="metric-spaces.metric-spaces.html#5090" class="Function">type-Metric-Space</a> <a id="2126" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1735" class="Bound">A</a> <a id="2128" class="Symbol">→</a> <a id="2130" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2133" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1722" class="Bound">l2</a>
  <a id="2138" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2059" class="Function">is-limit-cauchy-approximation-Metric-Space</a> <a id="2181" class="Symbol">=</a>
    <a id="2187" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2197" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2199" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1814" class="Function">is-limit-cauchy-approximation-prop-Metric-Space</a>
</pre>
## Properties

### Saturation of the limit

<pre class="Agda"><a id="2304" class="Keyword">module</a> <a id="2311" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2311" class="Module">_</a>
  <a id="2315" class="Symbol">{</a><a id="2316" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2316" class="Bound">l1</a> <a id="2319" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2319" class="Bound">l2</a> <a id="2322" class="Symbol">:</a> <a id="2324" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2329" class="Symbol">}</a> <a id="2331" class="Symbol">(</a><a id="2332" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2332" class="Bound">A</a> <a id="2334" class="Symbol">:</a> <a id="2336" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="2349" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2316" class="Bound">l1</a> <a id="2352" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2319" class="Bound">l2</a><a id="2354" class="Symbol">)</a>
  <a id="2358" class="Symbol">(</a><a id="2359" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2359" class="Bound">f</a> <a id="2361" class="Symbol">:</a> <a id="2363" href="metric-spaces.cauchy-approximations-metric-spaces.html#1957" class="Function">cauchy-approximation-Metric-Space</a> <a id="2397" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2332" class="Bound">A</a><a id="2398" class="Symbol">)</a>
  <a id="2402" class="Symbol">(</a><a id="2403" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2403" class="Bound">x</a> <a id="2405" class="Symbol">:</a> <a id="2407" href="metric-spaces.metric-spaces.html#5090" class="Function">type-Metric-Space</a> <a id="2425" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2332" class="Bound">A</a><a id="2426" class="Symbol">)</a>
  <a id="2430" class="Keyword">where</a>

  <a id="2439" class="Keyword">abstract</a>
    <a id="2452" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2452" class="Function">saturated-is-limit-cauchy-approximation-Metric-Space</a> <a id="2505" class="Symbol">:</a>
      <a id="2513" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2059" class="Function">is-limit-cauchy-approximation-Metric-Space</a> <a id="2556" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2332" class="Bound">A</a> <a id="2558" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2359" class="Bound">f</a> <a id="2560" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2403" class="Bound">x</a> <a id="2562" class="Symbol">→</a>
      <a id="2570" class="Symbol">(</a><a id="2571" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2571" class="Bound">ε</a> <a id="2573" class="Symbol">:</a> <a id="2575" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a><a id="2577" class="Symbol">)</a> <a id="2579" class="Symbol">→</a>
      <a id="2587" href="metric-spaces.metric-spaces.html#5726" class="Function">neighborhood-Metric-Space</a> <a id="2613" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2332" class="Bound">A</a> <a id="2615" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2571" class="Bound">ε</a>
        <a id="2625" class="Symbol">(</a> <a id="2627" href="metric-spaces.cauchy-approximations-metric-spaces.html#2223" class="Function">map-cauchy-approximation-Metric-Space</a> <a id="2665" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2332" class="Bound">A</a> <a id="2667" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2359" class="Bound">f</a> <a id="2669" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2571" class="Bound">ε</a><a id="2670" class="Symbol">)</a>
        <a id="2680" class="Symbol">(</a> <a id="2682" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2403" class="Bound">x</a><a id="2683" class="Symbol">)</a>
    <a id="2689" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2452" class="Function">saturated-is-limit-cauchy-approximation-Metric-Space</a> <a id="2742" class="Symbol">=</a>
      <a id="2750" href="metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces.html#2317" class="Function">saturated-is-limit-cauchy-approximation-Pseudometric-Space</a>
        <a id="2817" class="Symbol">(</a> <a id="2819" href="metric-spaces.metric-spaces.html#4998" class="Function">pseudometric-Metric-Space</a> <a id="2845" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2332" class="Bound">A</a><a id="2846" class="Symbol">)</a>
        <a id="2856" class="Symbol">(</a> <a id="2858" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2359" class="Bound">f</a><a id="2859" class="Symbol">)</a>
        <a id="2869" class="Symbol">(</a> <a id="2871" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2403" class="Bound">x</a><a id="2872" class="Symbol">)</a>
</pre>
### Limits in a metric space are unique

<pre class="Agda"><a id="2928" class="Keyword">module</a> <a id="2935" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2935" class="Module">_</a>
  <a id="2939" class="Symbol">{</a><a id="2940" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2940" class="Bound">l1</a> <a id="2943" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2943" class="Bound">l2</a> <a id="2946" class="Symbol">:</a> <a id="2948" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2953" class="Symbol">}</a> <a id="2955" class="Symbol">(</a><a id="2956" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2956" class="Bound">A</a> <a id="2958" class="Symbol">:</a> <a id="2960" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="2973" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2940" class="Bound">l1</a> <a id="2976" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2943" class="Bound">l2</a><a id="2978" class="Symbol">)</a>
  <a id="2982" class="Symbol">(</a><a id="2983" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2983" class="Bound">f</a> <a id="2985" class="Symbol">:</a> <a id="2987" href="metric-spaces.cauchy-approximations-metric-spaces.html#1957" class="Function">cauchy-approximation-Metric-Space</a> <a id="3021" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2956" class="Bound">A</a><a id="3022" class="Symbol">)</a>
  <a id="3026" class="Symbol">(</a><a id="3027" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3027" class="Bound">x</a> <a id="3029" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3029" class="Bound">y</a> <a id="3031" class="Symbol">:</a> <a id="3033" href="metric-spaces.metric-spaces.html#5090" class="Function">type-Metric-Space</a> <a id="3051" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2956" class="Bound">A</a><a id="3052" class="Symbol">)</a>
  <a id="3056" class="Keyword">where</a>

  <a id="3065" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3065" class="Function">all-sim-is-limit-cauchy-approximation-Metric-Space</a> <a id="3116" class="Symbol">:</a>
    <a id="3122" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2059" class="Function">is-limit-cauchy-approximation-Metric-Space</a> <a id="3165" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2956" class="Bound">A</a> <a id="3167" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2983" class="Bound">f</a> <a id="3169" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3027" class="Bound">x</a> <a id="3171" class="Symbol">→</a>
    <a id="3177" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2059" class="Function">is-limit-cauchy-approximation-Metric-Space</a> <a id="3220" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2956" class="Bound">A</a> <a id="3222" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2983" class="Bound">f</a> <a id="3224" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3029" class="Bound">y</a> <a id="3226" class="Symbol">→</a>
    <a id="3232" href="metric-spaces.metric-spaces.html#9205" class="Function">sim-Metric-Space</a> <a id="3249" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2956" class="Bound">A</a> <a id="3251" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3027" class="Bound">x</a> <a id="3253" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3029" class="Bound">y</a>
  <a id="3257" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3065" class="Function">all-sim-is-limit-cauchy-approximation-Metric-Space</a> <a id="3308" class="Symbol">=</a>
    <a id="3314" href="metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces.html#2958" class="Function">all-sim-is-limit-cauchy-approximation-Pseudometric-Space</a>
      <a id="3377" class="Symbol">(</a> <a id="3379" href="metric-spaces.metric-spaces.html#4998" class="Function">pseudometric-Metric-Space</a> <a id="3405" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2956" class="Bound">A</a><a id="3406" class="Symbol">)</a>
      <a id="3414" class="Symbol">(</a> <a id="3416" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2983" class="Bound">f</a><a id="3417" class="Symbol">)</a>
      <a id="3425" class="Symbol">(</a> <a id="3427" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3027" class="Bound">x</a><a id="3428" class="Symbol">)</a>
      <a id="3436" class="Symbol">(</a> <a id="3438" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3029" class="Bound">y</a><a id="3439" class="Symbol">)</a>

  <a id="3444" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3444" class="Function">all-eq-is-limit-cauchy-approximation-Metric-Space</a> <a id="3494" class="Symbol">:</a>
    <a id="3500" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2059" class="Function">is-limit-cauchy-approximation-Metric-Space</a> <a id="3543" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2956" class="Bound">A</a> <a id="3545" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2983" class="Bound">f</a> <a id="3547" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3027" class="Bound">x</a> <a id="3549" class="Symbol">→</a>
    <a id="3555" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2059" class="Function">is-limit-cauchy-approximation-Metric-Space</a> <a id="3598" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2956" class="Bound">A</a> <a id="3600" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2983" class="Bound">f</a> <a id="3602" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3029" class="Bound">y</a> <a id="3604" class="Symbol">→</a>
    <a id="3610" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3027" class="Bound">x</a> <a id="3612" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="3614" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3029" class="Bound">y</a>
  <a id="3618" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3444" class="Function">all-eq-is-limit-cauchy-approximation-Metric-Space</a> <a id="3668" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3668" class="Bound">lim-x</a> <a id="3674" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3674" class="Bound">lim-y</a> <a id="3680" class="Symbol">=</a>
    <a id="3686" href="metric-spaces.metric-spaces.html#11651" class="Function">eq-sim-Metric-Space</a>
      <a id="3712" class="Symbol">(</a> <a id="3714" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2956" class="Bound">A</a><a id="3715" class="Symbol">)</a>
      <a id="3723" class="Symbol">(</a> <a id="3725" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3027" class="Bound">x</a><a id="3726" class="Symbol">)</a>
      <a id="3734" class="Symbol">(</a> <a id="3736" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3029" class="Bound">y</a><a id="3737" class="Symbol">)</a>
      <a id="3745" class="Symbol">(</a> <a id="3747" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3065" class="Function">all-sim-is-limit-cauchy-approximation-Metric-Space</a> <a id="3798" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3668" class="Bound">lim-x</a> <a id="3804" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#3674" class="Bound">lim-y</a><a id="3809" class="Symbol">)</a>
</pre>
## See also

- [Convergent cauchy approximations](metric-spaces.convergent-cauchy-approximations-metric-spaces.md)
  are Cauchy approximations with a limit.

## References

Our definition of limit of Cauchy approximation follows Definition 11.2.10 of
{{#cite UF13}}.

{{#bibliography}}
