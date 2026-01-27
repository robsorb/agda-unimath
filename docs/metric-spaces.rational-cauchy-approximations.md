# Rational Cauchy approximations

<pre class="Agda"><a id="43" class="Keyword">module</a> <a id="50" href="metric-spaces.rational-cauchy-approximations.html" class="Module">metric-spaces.rational-cauchy-approximations</a> <a id="95" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="151" class="Keyword">open</a> <a id="156" class="Keyword">import</a> <a id="163" href="elementary-number-theory.absolute-value-rational-numbers.html" class="Module">elementary-number-theory.absolute-value-rational-numbers</a>
<a id="220" class="Keyword">open</a> <a id="225" class="Keyword">import</a> <a id="232" href="elementary-number-theory.distance-rational-numbers.html" class="Module">elementary-number-theory.distance-rational-numbers</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="elementary-number-theory.inequality-rational-numbers.html" class="Module">elementary-number-theory.inequality-rational-numbers</a>
<a id="348" class="Keyword">open</a> <a id="353" class="Keyword">import</a> <a id="360" href="elementary-number-theory.positive-rational-numbers.html" class="Module">elementary-number-theory.positive-rational-numbers</a>
<a id="411" class="Keyword">open</a> <a id="416" class="Keyword">import</a> <a id="423" href="elementary-number-theory.rational-numbers.html" class="Module">elementary-number-theory.rational-numbers</a>

<a id="466" class="Keyword">open</a> <a id="471" class="Keyword">import</a> <a id="478" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="510" class="Keyword">open</a> <a id="515" class="Keyword">import</a> <a id="522" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="546" class="Keyword">open</a> <a id="551" class="Keyword">import</a> <a id="558" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="578" class="Keyword">open</a> <a id="583" class="Keyword">import</a> <a id="590" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="618" class="Keyword">open</a> <a id="623" class="Keyword">import</a> <a id="630" href="metric-spaces.cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.cauchy-approximations-metric-spaces</a>
<a id="680" class="Keyword">open</a> <a id="685" class="Keyword">import</a> <a id="692" href="metric-spaces.complete-metric-spaces.html" class="Module">metric-spaces.complete-metric-spaces</a>
<a id="729" class="Keyword">open</a> <a id="734" class="Keyword">import</a> <a id="741" href="metric-spaces.convergent-cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.convergent-cauchy-approximations-metric-spaces</a>
<a id="802" class="Keyword">open</a> <a id="807" class="Keyword">import</a> <a id="814" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.limits-of-cauchy-approximations-metric-spaces</a>
<a id="874" class="Keyword">open</a> <a id="879" class="Keyword">import</a> <a id="886" href="metric-spaces.metric-space-of-rational-numbers.html" class="Module">metric-spaces.metric-space-of-rational-numbers</a>
<a id="933" class="Keyword">open</a> <a id="938" class="Keyword">import</a> <a id="945" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
<a id="973" class="Keyword">open</a> <a id="978" class="Keyword">import</a> <a id="985" href="metric-spaces.short-functions-metric-spaces.html" class="Module">metric-spaces.short-functions-metric-spaces</a>

<a id="1030" class="Keyword">open</a> <a id="1035" class="Keyword">import</a> <a id="1042" href="real-numbers.cauchy-completeness-dedekind-real-numbers.html" class="Module">real-numbers.cauchy-completeness-dedekind-real-numbers</a>
<a id="1097" class="Keyword">open</a> <a id="1102" class="Keyword">import</a> <a id="1109" href="real-numbers.dedekind-real-numbers.html" class="Module">real-numbers.dedekind-real-numbers</a>
<a id="1144" class="Keyword">open</a> <a id="1149" class="Keyword">import</a> <a id="1156" href="real-numbers.metric-space-of-real-numbers.html" class="Module">real-numbers.metric-space-of-real-numbers</a>
<a id="1198" class="Keyword">open</a> <a id="1203" class="Keyword">import</a> <a id="1210" href="real-numbers.rational-real-numbers.html" class="Module">real-numbers.rational-real-numbers</a>
</pre>
</details>

## Idea

{{#concept "Rational Cauchy approximations" Agda=cauchy-approximation-ℚ}} are
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
the
[metric space of rational numbers](metric-spaces.metric-space-of-rational-numbers.md).

## Definitions

### The type of rational Cauchy approximations

<pre class="Agda"><a id="cauchy-approximation-ℚ"></a><a id="1594" href="metric-spaces.rational-cauchy-approximations.html#1594" class="Function">cauchy-approximation-ℚ</a> <a id="1617" class="Symbol">:</a> <a id="1619" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1622" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1628" href="metric-spaces.rational-cauchy-approximations.html#1594" class="Function">cauchy-approximation-ℚ</a> <a id="1651" class="Symbol">=</a>
  <a id="1655" href="metric-spaces.cauchy-approximations-metric-spaces.html#1957" class="Function">cauchy-approximation-Metric-Space</a> <a id="1689" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a>

<a id="map-cauchy-approximation-ℚ"></a><a id="1705" href="metric-spaces.rational-cauchy-approximations.html#1705" class="Function">map-cauchy-approximation-ℚ</a> <a id="1732" class="Symbol">:</a> <a id="1734" href="metric-spaces.rational-cauchy-approximations.html#1594" class="Function">cauchy-approximation-ℚ</a> <a id="1757" class="Symbol">→</a> <a id="1759" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a> <a id="1762" class="Symbol">→</a> <a id="1764" href="elementary-number-theory.rational-numbers.html#2278" class="Function">ℚ</a>
<a id="1766" href="metric-spaces.rational-cauchy-approximations.html#1705" class="Function">map-cauchy-approximation-ℚ</a> <a id="1793" class="Symbol">=</a>
  <a id="1797" href="metric-spaces.cauchy-approximations-metric-spaces.html#2223" class="Function">map-cauchy-approximation-Metric-Space</a>
    <a id="1839" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a>

<a id="is-cauchy-map-cauchy-approximation-ℚ"></a><a id="1855" href="metric-spaces.rational-cauchy-approximations.html#1855" class="Function">is-cauchy-map-cauchy-approximation-ℚ</a> <a id="1892" class="Symbol">:</a>
  <a id="1896" class="Symbol">(</a><a id="1897" href="metric-spaces.rational-cauchy-approximations.html#1897" class="Bound">f</a> <a id="1899" class="Symbol">:</a> <a id="1901" href="metric-spaces.rational-cauchy-approximations.html#1594" class="Function">cauchy-approximation-ℚ</a><a id="1923" class="Symbol">)</a> <a id="1925" class="Symbol">→</a>
  <a id="1929" href="metric-spaces.cauchy-approximations-metric-spaces.html#1777" class="Function">is-cauchy-approximation-Metric-Space</a>
    <a id="1970" class="Symbol">(</a> <a id="1972" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a><a id="1986" class="Symbol">)</a>
    <a id="1992" class="Symbol">(</a> <a id="1994" href="metric-spaces.rational-cauchy-approximations.html#1705" class="Function">map-cauchy-approximation-ℚ</a> <a id="2021" href="metric-spaces.rational-cauchy-approximations.html#1897" class="Bound">f</a><a id="2022" class="Symbol">)</a>
<a id="2024" href="metric-spaces.rational-cauchy-approximations.html#1855" class="Function">is-cauchy-map-cauchy-approximation-ℚ</a> <a id="2061" class="Symbol">=</a>
  <a id="2065" href="metric-spaces.cauchy-approximations-metric-spaces.html#2433" class="Function">is-cauchy-approximation-map-cauchy-approximation-Metric-Space</a>
    <a id="2131" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a>
</pre>
## Properties

### The distance between two values `f ε` and `f δ` of a rational Cauchy approximation is bounded by `ε + δ`

<pre class="Agda"><a id="bound-dist-map-cauchy-approximation-ℚ"></a><a id="2284" href="metric-spaces.rational-cauchy-approximations.html#2284" class="Function">bound-dist-map-cauchy-approximation-ℚ</a> <a id="2322" class="Symbol">:</a>
  <a id="2326" class="Symbol">(</a><a id="2327" href="metric-spaces.rational-cauchy-approximations.html#2327" class="Bound">f</a> <a id="2329" class="Symbol">:</a> <a id="2331" href="metric-spaces.rational-cauchy-approximations.html#1594" class="Function">cauchy-approximation-ℚ</a><a id="2353" class="Symbol">)</a> <a id="2355" class="Symbol">→</a>
  <a id="2359" class="Symbol">(</a><a id="2360" href="metric-spaces.rational-cauchy-approximations.html#2360" class="Bound">ε</a> <a id="2362" href="metric-spaces.rational-cauchy-approximations.html#2362" class="Bound">δ</a> <a id="2364" class="Symbol">:</a> <a id="2366" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a><a id="2368" class="Symbol">)</a> <a id="2370" class="Symbol">→</a>
  <a id="2374" href="elementary-number-theory.inequality-rational-numbers.html#2922" class="Function">leq-ℚ</a>
    <a id="2384" class="Symbol">(</a> <a id="2386" href="elementary-number-theory.distance-rational-numbers.html#1938" class="Function">rational-dist-ℚ</a>
      <a id="2408" class="Symbol">(</a> <a id="2410" href="metric-spaces.rational-cauchy-approximations.html#1705" class="Function">map-cauchy-approximation-ℚ</a> <a id="2437" href="metric-spaces.rational-cauchy-approximations.html#2327" class="Bound">f</a> <a id="2439" href="metric-spaces.rational-cauchy-approximations.html#2360" class="Bound">ε</a><a id="2440" class="Symbol">)</a>
      <a id="2448" class="Symbol">(</a> <a id="2450" href="metric-spaces.rational-cauchy-approximations.html#1705" class="Function">map-cauchy-approximation-ℚ</a> <a id="2477" href="metric-spaces.rational-cauchy-approximations.html#2327" class="Bound">f</a> <a id="2479" href="metric-spaces.rational-cauchy-approximations.html#2362" class="Bound">δ</a><a id="2480" class="Symbol">))</a>
    <a id="2487" class="Symbol">(</a> <a id="2489" href="elementary-number-theory.positive-rational-numbers.html#4840" class="Function">rational-ℚ⁺</a> <a id="2501" class="Symbol">(</a><a id="2502" href="metric-spaces.rational-cauchy-approximations.html#2360" class="Bound">ε</a> <a id="2504" href="elementary-number-theory.positive-rational-numbers.html#11024" class="Function Operator">+ℚ⁺</a> <a id="2508" href="metric-spaces.rational-cauchy-approximations.html#2362" class="Bound">δ</a><a id="2509" class="Symbol">))</a>
<a id="2512" href="metric-spaces.rational-cauchy-approximations.html#2284" class="Function">bound-dist-map-cauchy-approximation-ℚ</a> <a id="2550" href="metric-spaces.rational-cauchy-approximations.html#2550" class="Bound">f</a> <a id="2552" href="metric-spaces.rational-cauchy-approximations.html#2552" class="Bound">ε</a> <a id="2554" href="metric-spaces.rational-cauchy-approximations.html#2554" class="Bound">δ</a> <a id="2556" class="Symbol">=</a>
  <a id="2560" href="metric-spaces.metric-space-of-rational-numbers.html#7346" class="Function">leq-dist-neighborhood-ℚ</a>
    <a id="2588" class="Symbol">(</a> <a id="2590" href="metric-spaces.rational-cauchy-approximations.html#2552" class="Bound">ε</a> <a id="2592" href="elementary-number-theory.positive-rational-numbers.html#11024" class="Function Operator">+ℚ⁺</a> <a id="2596" href="metric-spaces.rational-cauchy-approximations.html#2554" class="Bound">δ</a><a id="2597" class="Symbol">)</a>
    <a id="2603" class="Symbol">(</a> <a id="2605" href="metric-spaces.rational-cauchy-approximations.html#1705" class="Function">map-cauchy-approximation-ℚ</a> <a id="2632" href="metric-spaces.rational-cauchy-approximations.html#2550" class="Bound">f</a> <a id="2634" href="metric-spaces.rational-cauchy-approximations.html#2552" class="Bound">ε</a><a id="2635" class="Symbol">)</a>
    <a id="2641" class="Symbol">(</a> <a id="2643" href="metric-spaces.rational-cauchy-approximations.html#1705" class="Function">map-cauchy-approximation-ℚ</a> <a id="2670" href="metric-spaces.rational-cauchy-approximations.html#2550" class="Bound">f</a> <a id="2672" href="metric-spaces.rational-cauchy-approximations.html#2554" class="Bound">δ</a><a id="2673" class="Symbol">)</a>
    <a id="2679" class="Symbol">(</a> <a id="2681" href="metric-spaces.rational-cauchy-approximations.html#1855" class="Function">is-cauchy-map-cauchy-approximation-ℚ</a> <a id="2718" href="metric-spaces.rational-cauchy-approximations.html#2550" class="Bound">f</a> <a id="2720" href="metric-spaces.rational-cauchy-approximations.html#2552" class="Bound">ε</a> <a id="2722" href="metric-spaces.rational-cauchy-approximations.html#2554" class="Bound">δ</a><a id="2723" class="Symbol">)</a>
</pre>
### Any rational Cauchy approximation has a limit in the reals

<pre class="Agda"><a id="real-limit-cauchy-approximation-ℚ"></a><a id="2802" href="metric-spaces.rational-cauchy-approximations.html#2802" class="Function">real-limit-cauchy-approximation-ℚ</a> <a id="2836" class="Symbol">:</a> <a id="2838" href="metric-spaces.rational-cauchy-approximations.html#1594" class="Function">cauchy-approximation-ℚ</a> <a id="2861" class="Symbol">→</a> <a id="2863" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="2865" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2871" href="metric-spaces.rational-cauchy-approximations.html#2802" class="Function">real-limit-cauchy-approximation-ℚ</a> <a id="2905" href="metric-spaces.rational-cauchy-approximations.html#2905" class="Bound">f</a> <a id="2907" class="Symbol">=</a>
  <a id="2911" href="metric-spaces.complete-metric-spaces.html#5021" class="Function">limit-cauchy-approximation-Complete-Metric-Space</a>
    <a id="2964" class="Symbol">(</a> <a id="2966" href="real-numbers.cauchy-completeness-dedekind-real-numbers.html#18662" class="Function">complete-metric-space-ℝ</a> <a id="2990" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="2995" class="Symbol">)</a>
    <a id="3001" class="Symbol">(</a> <a id="3003" href="metric-spaces.cauchy-approximations-metric-spaces.html#3469" class="Function">map-short-function-cauchy-approximation-Metric-Space</a>
      <a id="3062" class="Symbol">(</a> <a id="3064" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a><a id="3078" class="Symbol">)</a>
      <a id="3086" class="Symbol">(</a> <a id="3088" href="real-numbers.metric-space-of-real-numbers.html#8513" class="Function">metric-space-ℝ</a> <a id="3103" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="3108" class="Symbol">)</a>
      <a id="3116" class="Symbol">(</a> <a id="3118" href="metric-spaces.short-functions-metric-spaces.html#9723" class="Function">short-isometry-Metric-Space</a>
        <a id="3154" class="Symbol">(</a> <a id="3156" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a><a id="3170" class="Symbol">)</a>
        <a id="3180" class="Symbol">(</a> <a id="3182" href="real-numbers.metric-space-of-real-numbers.html#8513" class="Function">metric-space-ℝ</a> <a id="3197" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="3202" class="Symbol">)</a>
        <a id="3212" class="Symbol">(</a> <a id="3214" href="real-numbers.metric-space-of-real-numbers.html#12499" class="Function">isometry-metric-space-real-ℚ</a><a id="3242" class="Symbol">))</a>
      <a id="3251" class="Symbol">(</a> <a id="3253" href="metric-spaces.rational-cauchy-approximations.html#2905" class="Bound">f</a><a id="3254" class="Symbol">))</a>
</pre>