# Rational approximations of zero

<pre class="Agda"><a id="44" class="Symbol">{-#</a> <a id="48" class="Keyword">OPTIONS</a> <a id="56" class="Pragma">--lossy-unification</a> <a id="76" class="Symbol">#-}</a>

<a id="81" class="Keyword">module</a> <a id="88" href="metric-spaces.rational-approximations-of-zero.html" class="Module">metric-spaces.rational-approximations-of-zero</a> <a id="134" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="190" class="Keyword">open</a> <a id="195" class="Keyword">import</a> <a id="202" href="elementary-number-theory.absolute-value-rational-numbers.html" class="Module">elementary-number-theory.absolute-value-rational-numbers</a>
<a id="259" class="Keyword">open</a> <a id="264" class="Keyword">import</a> <a id="271" href="elementary-number-theory.addition-rational-numbers.html" class="Module">elementary-number-theory.addition-rational-numbers</a>
<a id="322" class="Keyword">open</a> <a id="327" class="Keyword">import</a> <a id="334" href="elementary-number-theory.difference-rational-numbers.html" class="Module">elementary-number-theory.difference-rational-numbers</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="elementary-number-theory.distance-rational-numbers.html" class="Module">elementary-number-theory.distance-rational-numbers</a>
<a id="450" class="Keyword">open</a> <a id="455" class="Keyword">import</a> <a id="462" href="elementary-number-theory.inequality-rational-numbers.html" class="Module">elementary-number-theory.inequality-rational-numbers</a>
<a id="515" class="Keyword">open</a> <a id="520" class="Keyword">import</a> <a id="527" href="elementary-number-theory.nonnegative-rational-numbers.html" class="Module">elementary-number-theory.nonnegative-rational-numbers</a>
<a id="581" class="Keyword">open</a> <a id="586" class="Keyword">import</a> <a id="593" href="elementary-number-theory.positive-rational-numbers.html" class="Module">elementary-number-theory.positive-rational-numbers</a>
<a id="644" class="Keyword">open</a> <a id="649" class="Keyword">import</a> <a id="656" href="elementary-number-theory.rational-numbers.html" class="Module">elementary-number-theory.rational-numbers</a>

<a id="699" class="Keyword">open</a> <a id="704" class="Keyword">import</a> <a id="711" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="758" class="Keyword">open</a> <a id="763" class="Keyword">import</a> <a id="770" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="802" class="Keyword">open</a> <a id="807" class="Keyword">import</a> <a id="814" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="838" class="Keyword">open</a> <a id="843" class="Keyword">import</a> <a id="850" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="896" class="Keyword">open</a> <a id="901" class="Keyword">import</a> <a id="908" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="934" class="Keyword">open</a> <a id="939" class="Keyword">import</a> <a id="946" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="970" class="Keyword">open</a> <a id="975" class="Keyword">import</a> <a id="982" href="foundation.retractions.html" class="Module">foundation.retractions</a>
<a id="1005" class="Keyword">open</a> <a id="1010" class="Keyword">import</a> <a id="1017" href="foundation.sections.html" class="Module">foundation.sections</a>
<a id="1037" class="Keyword">open</a> <a id="1042" class="Keyword">import</a> <a id="1049" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="1069" class="Keyword">open</a> <a id="1074" class="Keyword">import</a> <a id="1081" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="1124" class="Keyword">open</a> <a id="1129" class="Keyword">import</a> <a id="1136" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="1164" class="Keyword">open</a> <a id="1169" class="Keyword">import</a> <a id="1176" href="metric-spaces.cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.cauchy-approximations-metric-spaces</a>
<a id="1226" class="Keyword">open</a> <a id="1231" class="Keyword">import</a> <a id="1238" href="metric-spaces.convergent-cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.convergent-cauchy-approximations-metric-spaces</a>
<a id="1299" class="Keyword">open</a> <a id="1304" class="Keyword">import</a> <a id="1311" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.limits-of-cauchy-approximations-metric-spaces</a>
<a id="1371" class="Keyword">open</a> <a id="1376" class="Keyword">import</a> <a id="1383" href="metric-spaces.metric-space-of-rational-numbers.html" class="Module">metric-spaces.metric-space-of-rational-numbers</a>
<a id="1430" class="Keyword">open</a> <a id="1435" class="Keyword">import</a> <a id="1442" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
<a id="1470" class="Keyword">open</a> <a id="1475" class="Keyword">import</a> <a id="1482" href="metric-spaces.rational-cauchy-approximations.html" class="Module">metric-spaces.rational-cauchy-approximations</a>
</pre>
</details>

## Idea

A map from the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
to the [rationals](elementary-number-theory.rational-numbers.md) `f : ℚ⁺ → ℚ` is
a {{#concept "rational approximation of zero"  Agda=approximation-of-zero-ℚ}} if
`|f ε| ≤ ε` for all `ε : ℚ⁺`. The type of rational approximations of zero is
[equivalent](foundation.equivalences.md) to the type of
[rational Cauchy approximations](metric-spaces.rational-cauchy-approximations.md)
[converging](metric-spaces.convergent-cauchy-approximations-metric-spaces.md) to
zero.

## Definitions

### Rational approximations of zero

<pre class="Agda"><a id="2177" class="Keyword">module</a> <a id="2184" href="metric-spaces.rational-approximations-of-zero.html#2184" class="Module">_</a>
  <a id="2188" class="Symbol">(</a><a id="2189" href="metric-spaces.rational-approximations-of-zero.html#2189" class="Bound">f</a> <a id="2191" class="Symbol">:</a> <a id="2193" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a> <a id="2196" class="Symbol">→</a> <a id="2198" href="elementary-number-theory.rational-numbers.html#2278" class="Function">ℚ</a><a id="2199" class="Symbol">)</a>
  <a id="2203" class="Keyword">where</a>

  <a id="2212" href="metric-spaces.rational-approximations-of-zero.html#2212" class="Function">subtype-approximation-of-zero-ℚ</a> <a id="2244" class="Symbol">:</a> <a id="2246" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2251" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="2259" href="metric-spaces.rational-approximations-of-zero.html#2212" class="Function">subtype-approximation-of-zero-ℚ</a> <a id="2291" class="Symbol">=</a>
    <a id="2297" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="2310" class="Symbol">(</a> <a id="2312" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a><a id="2314" class="Symbol">)</a>
      <a id="2322" class="Symbol">(</a> <a id="2324" class="Symbol">λ</a> <a id="2326" href="metric-spaces.rational-approximations-of-zero.html#2326" class="Bound">ε</a> <a id="2328" class="Symbol">→</a> <a id="2330" href="elementary-number-theory.inequality-rational-numbers.html#2832" class="Function">leq-ℚ-Prop</a> <a id="2341" class="Symbol">(</a><a id="2342" href="elementary-number-theory.absolute-value-rational-numbers.html#1619" class="Function">rational-abs-ℚ</a> <a id="2357" class="Symbol">(</a><a id="2358" href="metric-spaces.rational-approximations-of-zero.html#2189" class="Bound">f</a> <a id="2360" href="metric-spaces.rational-approximations-of-zero.html#2326" class="Bound">ε</a><a id="2361" class="Symbol">))</a> <a id="2364" class="Symbol">(</a><a id="2365" href="elementary-number-theory.positive-rational-numbers.html#4840" class="Function">rational-ℚ⁺</a> <a id="2377" href="metric-spaces.rational-approximations-of-zero.html#2326" class="Bound">ε</a><a id="2378" class="Symbol">))</a>

  <a id="2384" href="metric-spaces.rational-approximations-of-zero.html#2384" class="Function">is-approximation-of-zero-ℚ</a> <a id="2411" class="Symbol">:</a> <a id="2413" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2416" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="2424" href="metric-spaces.rational-approximations-of-zero.html#2384" class="Function">is-approximation-of-zero-ℚ</a> <a id="2451" class="Symbol">=</a>
    <a id="2457" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2467" href="metric-spaces.rational-approximations-of-zero.html#2212" class="Function">subtype-approximation-of-zero-ℚ</a>

<a id="approximation-of-zero-ℚ"></a><a id="2500" href="metric-spaces.rational-approximations-of-zero.html#2500" class="Function">approximation-of-zero-ℚ</a> <a id="2524" class="Symbol">:</a> <a id="2526" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2529" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2535" href="metric-spaces.rational-approximations-of-zero.html#2500" class="Function">approximation-of-zero-ℚ</a> <a id="2559" class="Symbol">=</a> <a id="2561" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="2574" href="metric-spaces.rational-approximations-of-zero.html#2212" class="Function">subtype-approximation-of-zero-ℚ</a>

<a id="2607" class="Keyword">module</a> <a id="2614" href="metric-spaces.rational-approximations-of-zero.html#2614" class="Module">_</a>
  <a id="2618" class="Symbol">(</a><a id="2619" href="metric-spaces.rational-approximations-of-zero.html#2619" class="Bound">f</a> <a id="2621" class="Symbol">:</a> <a id="2623" href="metric-spaces.rational-approximations-of-zero.html#2500" class="Function">approximation-of-zero-ℚ</a><a id="2646" class="Symbol">)</a>
  <a id="2650" class="Keyword">where</a>

  <a id="2659" href="metric-spaces.rational-approximations-of-zero.html#2659" class="Function">map-approximation-of-zero-ℚ</a> <a id="2687" class="Symbol">:</a> <a id="2689" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a> <a id="2692" class="Symbol">→</a> <a id="2694" href="elementary-number-theory.rational-numbers.html#2278" class="Function">ℚ</a>
  <a id="2698" href="metric-spaces.rational-approximations-of-zero.html#2659" class="Function">map-approximation-of-zero-ℚ</a> <a id="2726" class="Symbol">=</a> <a id="2728" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2732" href="metric-spaces.rational-approximations-of-zero.html#2619" class="Bound">f</a>

  <a id="2737" href="metric-spaces.rational-approximations-of-zero.html#2737" class="Function">is-approximation-of-zero-map-approximation-of-zero-ℚ</a> <a id="2790" class="Symbol">:</a>
    <a id="2796" href="metric-spaces.rational-approximations-of-zero.html#2384" class="Function">is-approximation-of-zero-ℚ</a> <a id="2823" href="metric-spaces.rational-approximations-of-zero.html#2659" class="Function">map-approximation-of-zero-ℚ</a>
  <a id="2853" href="metric-spaces.rational-approximations-of-zero.html#2737" class="Function">is-approximation-of-zero-map-approximation-of-zero-ℚ</a> <a id="2906" class="Symbol">=</a> <a id="2908" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2912" href="metric-spaces.rational-approximations-of-zero.html#2619" class="Bound">f</a>
</pre>
### The type of rational Cauchy approximations converging to zero

<pre class="Agda"><a id="zero-limit-cauchy-approximation-ℚ"></a><a id="2994" href="metric-spaces.rational-approximations-of-zero.html#2994" class="Function">zero-limit-cauchy-approximation-ℚ</a> <a id="3028" class="Symbol">:</a> <a id="3030" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3033" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="3039" href="metric-spaces.rational-approximations-of-zero.html#2994" class="Function">zero-limit-cauchy-approximation-ℚ</a> <a id="3073" class="Symbol">=</a>
  <a id="3077" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a>
    <a id="3094" class="Symbol">(</a> <a id="3096" class="Symbol">λ</a> <a id="3098" href="metric-spaces.rational-approximations-of-zero.html#3098" class="Bound">f</a> <a id="3100" class="Symbol">→</a>
      <a id="3108" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1814" class="Function">is-limit-cauchy-approximation-prop-Metric-Space</a>
        <a id="3164" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a>
        <a id="3187" href="metric-spaces.rational-approximations-of-zero.html#3098" class="Bound">f</a>
        <a id="3197" href="elementary-number-theory.rational-numbers.html#3520" class="Function">zero-ℚ</a><a id="3203" class="Symbol">)</a>

<a id="3206" class="Keyword">module</a> <a id="3213" href="metric-spaces.rational-approximations-of-zero.html#3213" class="Module">_</a>
  <a id="3217" class="Symbol">(</a><a id="3218" href="metric-spaces.rational-approximations-of-zero.html#3218" class="Bound">f</a> <a id="3220" class="Symbol">:</a> <a id="3222" href="metric-spaces.rational-approximations-of-zero.html#2994" class="Function">zero-limit-cauchy-approximation-ℚ</a><a id="3255" class="Symbol">)</a>
  <a id="3259" class="Keyword">where</a>

  <a id="3268" href="metric-spaces.rational-approximations-of-zero.html#3268" class="Function">approximation-zero-limit-cauchy-approximation-ℚ</a> <a id="3316" class="Symbol">:</a>
    <a id="3322" href="metric-spaces.rational-cauchy-approximations.html#1594" class="Function">cauchy-approximation-ℚ</a>
  <a id="3347" href="metric-spaces.rational-approximations-of-zero.html#3268" class="Function">approximation-zero-limit-cauchy-approximation-ℚ</a> <a id="3395" class="Symbol">=</a> <a id="3397" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3401" href="metric-spaces.rational-approximations-of-zero.html#3218" class="Bound">f</a>

  <a id="3406" href="metric-spaces.rational-approximations-of-zero.html#3406" class="Function">map-zero-limit-cauchy-approximation-ℚ</a> <a id="3444" class="Symbol">:</a> <a id="3446" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a> <a id="3449" class="Symbol">→</a> <a id="3451" href="elementary-number-theory.rational-numbers.html#2278" class="Function">ℚ</a>
  <a id="3455" href="metric-spaces.rational-approximations-of-zero.html#3406" class="Function">map-zero-limit-cauchy-approximation-ℚ</a> <a id="3493" class="Symbol">=</a>
    <a id="3499" href="metric-spaces.rational-cauchy-approximations.html#1705" class="Function">map-cauchy-approximation-ℚ</a> <a id="3526" href="metric-spaces.rational-approximations-of-zero.html#3268" class="Function">approximation-zero-limit-cauchy-approximation-ℚ</a>

  <a id="3577" href="metric-spaces.rational-approximations-of-zero.html#3577" class="Function">is-cauchy-map-zero-limit-cauchy-approximation-ℚ</a> <a id="3625" class="Symbol">:</a>
    <a id="3631" href="metric-spaces.cauchy-approximations-metric-spaces.html#1777" class="Function">is-cauchy-approximation-Metric-Space</a>
      <a id="3674" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a>
      <a id="3695" href="metric-spaces.rational-approximations-of-zero.html#3406" class="Function">map-zero-limit-cauchy-approximation-ℚ</a>
  <a id="3735" href="metric-spaces.rational-approximations-of-zero.html#3577" class="Function">is-cauchy-map-zero-limit-cauchy-approximation-ℚ</a> <a id="3783" class="Symbol">=</a>
    <a id="3789" href="metric-spaces.rational-cauchy-approximations.html#1855" class="Function">is-cauchy-map-cauchy-approximation-ℚ</a>
      <a id="3832" href="metric-spaces.rational-approximations-of-zero.html#3268" class="Function">approximation-zero-limit-cauchy-approximation-ℚ</a>

  <a id="3883" href="metric-spaces.rational-approximations-of-zero.html#3883" class="Function">is-zero-limit-approximation-zero-limit-cauchy-approximation-ℚ</a> <a id="3945" class="Symbol">:</a>
    <a id="3951" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2059" class="Function">is-limit-cauchy-approximation-Metric-Space</a>
      <a id="4000" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a>
      <a id="4021" href="metric-spaces.rational-approximations-of-zero.html#3268" class="Function">approximation-zero-limit-cauchy-approximation-ℚ</a>
      <a id="4075" href="elementary-number-theory.rational-numbers.html#3520" class="Function">zero-ℚ</a>
  <a id="4084" href="metric-spaces.rational-approximations-of-zero.html#3883" class="Function">is-zero-limit-approximation-zero-limit-cauchy-approximation-ℚ</a> <a id="4146" class="Symbol">=</a> <a id="4148" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4152" href="metric-spaces.rational-approximations-of-zero.html#3218" class="Bound">f</a>
</pre>
## Properties

### The type of rational approximations of zero is equivalent to the type of Cauchy approximations converging to zero

<pre class="Agda"><a id="4301" class="Keyword">module</a> <a id="4308" href="metric-spaces.rational-approximations-of-zero.html#4308" class="Module">_</a>
  <a id="4312" class="Symbol">(</a><a id="4313" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="4315" class="Symbol">:</a> <a id="4317" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a> <a id="4320" class="Symbol">→</a> <a id="4322" href="elementary-number-theory.rational-numbers.html#2278" class="Function">ℚ</a><a id="4323" class="Symbol">)</a>
  <a id="4327" class="Symbol">(</a><a id="4328" href="metric-spaces.rational-approximations-of-zero.html#4328" class="Bound">is-approximation-of-zero-f</a> <a id="4355" class="Symbol">:</a> <a id="4357" href="metric-spaces.rational-approximations-of-zero.html#2384" class="Function">is-approximation-of-zero-ℚ</a> <a id="4384" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a><a id="4385" class="Symbol">)</a>
  <a id="4389" class="Keyword">where</a>

  <a id="4398" class="Keyword">abstract</a>
    <a id="4411" href="metric-spaces.rational-approximations-of-zero.html#4411" class="Function">is-cauchy-approximation-is-approximation-of-zero-ℚ</a> <a id="4462" class="Symbol">:</a>
      <a id="4470" href="metric-spaces.cauchy-approximations-metric-spaces.html#1777" class="Function">is-cauchy-approximation-Metric-Space</a>
        <a id="4515" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a>
        <a id="4538" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a>
    <a id="4544" href="metric-spaces.rational-approximations-of-zero.html#4411" class="Function">is-cauchy-approximation-is-approximation-of-zero-ℚ</a> <a id="4595" href="metric-spaces.rational-approximations-of-zero.html#4595" class="Bound">ε</a> <a id="4597" href="metric-spaces.rational-approximations-of-zero.html#4597" class="Bound">δ</a> <a id="4599" class="Symbol">=</a>
      <a id="4607" href="metric-spaces.metric-space-of-rational-numbers.html#7729" class="Function">neighborhood-leq-dist-ℚ</a>
        <a id="4639" class="Symbol">(</a> <a id="4641" href="metric-spaces.rational-approximations-of-zero.html#4595" class="Bound">ε</a> <a id="4643" href="elementary-number-theory.positive-rational-numbers.html#11024" class="Function Operator">+ℚ⁺</a> <a id="4647" href="metric-spaces.rational-approximations-of-zero.html#4597" class="Bound">δ</a><a id="4648" class="Symbol">)</a>
        <a id="4658" class="Symbol">(</a> <a id="4660" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="4662" href="metric-spaces.rational-approximations-of-zero.html#4595" class="Bound">ε</a><a id="4663" class="Symbol">)</a>
        <a id="4673" class="Symbol">(</a> <a id="4675" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="4677" href="metric-spaces.rational-approximations-of-zero.html#4597" class="Bound">δ</a><a id="4678" class="Symbol">)</a>
        <a id="4688" class="Symbol">(</a> <a id="4690" href="elementary-number-theory.inequality-rational-numbers.html#5083" class="Function">transitive-leq-ℚ</a>
          <a id="4717" class="Symbol">(</a> <a id="4719" href="elementary-number-theory.distance-rational-numbers.html#1938" class="Function">rational-dist-ℚ</a> <a id="4735" class="Symbol">(</a><a id="4736" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="4738" href="metric-spaces.rational-approximations-of-zero.html#4595" class="Bound">ε</a><a id="4739" class="Symbol">)</a> <a id="4741" class="Symbol">(</a><a id="4742" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="4744" href="metric-spaces.rational-approximations-of-zero.html#4597" class="Bound">δ</a><a id="4745" class="Symbol">))</a>
          <a id="4758" class="Symbol">(</a> <a id="4760" class="Symbol">(</a><a id="4761" href="elementary-number-theory.absolute-value-rational-numbers.html#1619" class="Function">rational-abs-ℚ</a> <a id="4776" class="Symbol">(</a><a id="4777" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="4779" href="metric-spaces.rational-approximations-of-zero.html#4595" class="Bound">ε</a><a id="4780" class="Symbol">))</a> <a id="4783" href="elementary-number-theory.addition-rational-numbers.html#1390" class="Function Operator">+ℚ</a> <a id="4786" class="Symbol">(</a><a id="4787" href="elementary-number-theory.absolute-value-rational-numbers.html#1619" class="Function">rational-abs-ℚ</a> <a id="4802" class="Symbol">(</a><a id="4803" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="4805" href="metric-spaces.rational-approximations-of-zero.html#4597" class="Bound">δ</a><a id="4806" class="Symbol">)))</a>
          <a id="4820" class="Symbol">(</a> <a id="4822" href="elementary-number-theory.positive-rational-numbers.html#4840" class="Function">rational-ℚ⁺</a> <a id="4834" class="Symbol">(</a><a id="4835" href="metric-spaces.rational-approximations-of-zero.html#4595" class="Bound">ε</a> <a id="4837" href="elementary-number-theory.positive-rational-numbers.html#11024" class="Function Operator">+ℚ⁺</a> <a id="4841" href="metric-spaces.rational-approximations-of-zero.html#4597" class="Bound">δ</a><a id="4842" class="Symbol">))</a>
          <a id="4855" class="Symbol">(</a> <a id="4857" href="elementary-number-theory.inequality-rational-numbers.html#11375" class="Function">preserves-leq-add-ℚ</a>
            <a id="4889" class="Symbol">{</a> <a id="4891" href="elementary-number-theory.absolute-value-rational-numbers.html#1619" class="Function">rational-abs-ℚ</a> <a id="4906" class="Symbol">(</a><a id="4907" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="4909" href="metric-spaces.rational-approximations-of-zero.html#4595" class="Bound">ε</a><a id="4910" class="Symbol">)}</a>
            <a id="4925" class="Symbol">{</a> <a id="4927" href="elementary-number-theory.positive-rational-numbers.html#4840" class="Function">rational-ℚ⁺</a> <a id="4939" href="metric-spaces.rational-approximations-of-zero.html#4595" class="Bound">ε</a><a id="4940" class="Symbol">}</a>
            <a id="4954" class="Symbol">{</a> <a id="4956" href="elementary-number-theory.absolute-value-rational-numbers.html#1619" class="Function">rational-abs-ℚ</a> <a id="4971" class="Symbol">(</a><a id="4972" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="4974" href="metric-spaces.rational-approximations-of-zero.html#4597" class="Bound">δ</a><a id="4975" class="Symbol">)}</a>
            <a id="4990" class="Symbol">{</a> <a id="4992" href="elementary-number-theory.positive-rational-numbers.html#4840" class="Function">rational-ℚ⁺</a> <a id="5004" href="metric-spaces.rational-approximations-of-zero.html#4597" class="Bound">δ</a><a id="5005" class="Symbol">}</a>
            <a id="5019" class="Symbol">(</a> <a id="5021" href="metric-spaces.rational-approximations-of-zero.html#4328" class="Bound">is-approximation-of-zero-f</a> <a id="5048" href="metric-spaces.rational-approximations-of-zero.html#4595" class="Bound">ε</a><a id="5049" class="Symbol">)</a>
            <a id="5063" class="Symbol">(</a> <a id="5065" href="metric-spaces.rational-approximations-of-zero.html#4328" class="Bound">is-approximation-of-zero-f</a> <a id="5092" href="metric-spaces.rational-approximations-of-zero.html#4597" class="Bound">δ</a><a id="5093" class="Symbol">))</a>
          <a id="5106" class="Symbol">(</a> <a id="5108" href="elementary-number-theory.distance-rational-numbers.html#5238" class="Function">leq-dist-add-abs-ℚ</a> <a id="5127" class="Symbol">(</a><a id="5128" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="5130" href="metric-spaces.rational-approximations-of-zero.html#4595" class="Bound">ε</a><a id="5131" class="Symbol">)</a> <a id="5133" class="Symbol">(</a><a id="5134" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="5136" href="metric-spaces.rational-approximations-of-zero.html#4597" class="Bound">δ</a><a id="5137" class="Symbol">)))</a>

  <a id="5144" href="metric-spaces.rational-approximations-of-zero.html#5144" class="Function">cauchy-approximation-is-approximation-of-zero-ℚ</a> <a id="5192" class="Symbol">:</a>
    <a id="5198" href="metric-spaces.rational-cauchy-approximations.html#1594" class="Function">cauchy-approximation-ℚ</a>
  <a id="5223" href="metric-spaces.rational-approximations-of-zero.html#5144" class="Function">cauchy-approximation-is-approximation-of-zero-ℚ</a> <a id="5271" class="Symbol">=</a>
    <a id="5277" class="Symbol">(</a><a id="5278" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="5280" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="5282" href="metric-spaces.rational-approximations-of-zero.html#4411" class="Function">is-cauchy-approximation-is-approximation-of-zero-ℚ</a><a id="5332" class="Symbol">)</a>

  <a id="5337" class="Keyword">abstract</a>
    <a id="5350" href="metric-spaces.rational-approximations-of-zero.html#5350" class="Function">is-zero-limit-is-approximation-of-zero-ℚ</a> <a id="5391" class="Symbol">:</a>
      <a id="5399" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2059" class="Function">is-limit-cauchy-approximation-Metric-Space</a>
        <a id="5450" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a>
        <a id="5473" href="metric-spaces.rational-approximations-of-zero.html#5144" class="Function">cauchy-approximation-is-approximation-of-zero-ℚ</a>
        <a id="5529" href="elementary-number-theory.rational-numbers.html#3520" class="Function">zero-ℚ</a>
    <a id="5540" href="metric-spaces.rational-approximations-of-zero.html#5350" class="Function">is-zero-limit-is-approximation-of-zero-ℚ</a> <a id="5581" href="metric-spaces.rational-approximations-of-zero.html#5581" class="Bound">ε</a> <a id="5583" href="metric-spaces.rational-approximations-of-zero.html#5583" class="Bound">δ</a> <a id="5585" class="Symbol">=</a>
      <a id="5593" href="metric-spaces.metric-space-of-rational-numbers.html#7729" class="Function">neighborhood-leq-dist-ℚ</a>
        <a id="5625" class="Symbol">(</a> <a id="5627" href="metric-spaces.rational-approximations-of-zero.html#5581" class="Bound">ε</a> <a id="5629" href="elementary-number-theory.positive-rational-numbers.html#11024" class="Function Operator">+ℚ⁺</a> <a id="5633" href="metric-spaces.rational-approximations-of-zero.html#5583" class="Bound">δ</a><a id="5634" class="Symbol">)</a>
        <a id="5644" class="Symbol">(</a> <a id="5646" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="5648" href="metric-spaces.rational-approximations-of-zero.html#5581" class="Bound">ε</a><a id="5649" class="Symbol">)</a>
        <a id="5659" class="Symbol">(</a> <a id="5661" href="elementary-number-theory.rational-numbers.html#3520" class="Function">zero-ℚ</a><a id="5667" class="Symbol">)</a>
        <a id="5677" class="Symbol">(</a> <a id="5679" href="elementary-number-theory.inequality-rational-numbers.html#5083" class="Function">transitive-leq-ℚ</a>
          <a id="5706" class="Symbol">(</a> <a id="5708" href="elementary-number-theory.absolute-value-rational-numbers.html#1619" class="Function">rational-abs-ℚ</a>
            <a id="5735" class="Symbol">(</a> <a id="5737" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="5739" href="metric-spaces.rational-approximations-of-zero.html#5581" class="Bound">ε</a> <a id="5741" href="elementary-number-theory.difference-rational-numbers.html#950" class="Function Operator">-ℚ</a> <a id="5744" href="elementary-number-theory.rational-numbers.html#3520" class="Function">zero-ℚ</a><a id="5750" class="Symbol">))</a>
          <a id="5763" class="Symbol">(</a> <a id="5765" href="elementary-number-theory.positive-rational-numbers.html#4840" class="Function">rational-ℚ⁺</a> <a id="5777" href="metric-spaces.rational-approximations-of-zero.html#5581" class="Bound">ε</a><a id="5778" class="Symbol">)</a>
          <a id="5790" class="Symbol">(</a> <a id="5792" href="elementary-number-theory.positive-rational-numbers.html#4840" class="Function">rational-ℚ⁺</a> <a id="5804" class="Symbol">(</a><a id="5805" href="metric-spaces.rational-approximations-of-zero.html#5581" class="Bound">ε</a> <a id="5807" href="elementary-number-theory.positive-rational-numbers.html#11024" class="Function Operator">+ℚ⁺</a> <a id="5811" href="metric-spaces.rational-approximations-of-zero.html#5583" class="Bound">δ</a><a id="5812" class="Symbol">))</a>
          <a id="5825" class="Symbol">(</a> <a id="5827" href="elementary-number-theory.positive-rational-numbers.html#18442" class="Function">leq-le-ℚ⁺</a> <a id="5837" class="Symbol">{</a><a id="5838" href="metric-spaces.rational-approximations-of-zero.html#5581" class="Bound">ε</a><a id="5839" class="Symbol">}</a> <a id="5841" class="Symbol">{</a><a id="5842" href="metric-spaces.rational-approximations-of-zero.html#5581" class="Bound">ε</a> <a id="5844" href="elementary-number-theory.positive-rational-numbers.html#11024" class="Function Operator">+ℚ⁺</a> <a id="5848" href="metric-spaces.rational-approximations-of-zero.html#5583" class="Bound">δ</a><a id="5849" class="Symbol">}</a> <a id="5851" class="Symbol">(</a><a id="5852" href="elementary-number-theory.positive-rational-numbers.html#20482" class="Function">le-left-add-ℚ⁺</a> <a id="5867" href="metric-spaces.rational-approximations-of-zero.html#5581" class="Bound">ε</a> <a id="5869" href="metric-spaces.rational-approximations-of-zero.html#5583" class="Bound">δ</a><a id="5870" class="Symbol">))</a>
          <a id="5883" class="Symbol">(</a> <a id="5885" href="foundation.transport-along-identifications.html#1082" class="Function">inv-tr</a>
            <a id="5904" class="Symbol">(</a> <a id="5906" class="Symbol">λ</a> <a id="5908" href="metric-spaces.rational-approximations-of-zero.html#5908" class="Bound">y</a> <a id="5910" class="Symbol">→</a> <a id="5912" href="elementary-number-theory.inequality-rational-numbers.html#2922" class="Function">leq-ℚ</a> <a id="5918" class="Symbol">(</a><a id="5919" href="elementary-number-theory.nonnegative-rational-numbers.html#2618" class="Function">rational-ℚ⁰⁺</a> <a id="5932" href="metric-spaces.rational-approximations-of-zero.html#5908" class="Bound">y</a><a id="5933" class="Symbol">)</a> <a id="5935" class="Symbol">(</a><a id="5936" href="elementary-number-theory.positive-rational-numbers.html#4840" class="Function">rational-ℚ⁺</a> <a id="5948" href="metric-spaces.rational-approximations-of-zero.html#5581" class="Bound">ε</a><a id="5949" class="Symbol">))</a>
              <a id="5966" class="Symbol">(</a> <a id="5968" href="elementary-number-theory.distance-rational-numbers.html#2714" class="Function">right-zero-law-dist-ℚ</a>
              <a id="6004" class="Symbol">(</a> <a id="6006" href="metric-spaces.rational-approximations-of-zero.html#4313" class="Bound">f</a> <a id="6008" href="metric-spaces.rational-approximations-of-zero.html#5581" class="Bound">ε</a><a id="6009" class="Symbol">))</a>
            <a id="6024" class="Symbol">(</a> <a id="6026" href="metric-spaces.rational-approximations-of-zero.html#4328" class="Bound">is-approximation-of-zero-f</a> <a id="6053" href="metric-spaces.rational-approximations-of-zero.html#5581" class="Bound">ε</a><a id="6054" class="Symbol">)))</a>

<a id="6059" class="Keyword">module</a> <a id="6066" href="metric-spaces.rational-approximations-of-zero.html#6066" class="Module">_</a>
  <a id="6070" class="Symbol">(</a><a id="6071" href="metric-spaces.rational-approximations-of-zero.html#6071" class="Bound">f</a> <a id="6073" class="Symbol">:</a> <a id="6075" href="metric-spaces.rational-approximations-of-zero.html#2500" class="Function">approximation-of-zero-ℚ</a><a id="6098" class="Symbol">)</a>
  <a id="6102" class="Keyword">where</a>

  <a id="6111" href="metric-spaces.rational-approximations-of-zero.html#6111" class="Function">cauchy-approximation-of-zero-ℚ</a> <a id="6142" class="Symbol">:</a> <a id="6144" href="metric-spaces.rational-cauchy-approximations.html#1594" class="Function">cauchy-approximation-ℚ</a>
  <a id="6169" href="metric-spaces.rational-approximations-of-zero.html#6111" class="Function">cauchy-approximation-of-zero-ℚ</a> <a id="6200" class="Symbol">=</a>
    <a id="6206" href="metric-spaces.rational-approximations-of-zero.html#5144" class="Function">cauchy-approximation-is-approximation-of-zero-ℚ</a>
      <a id="6260" class="Symbol">(</a> <a id="6262" href="metric-spaces.rational-approximations-of-zero.html#2659" class="Function">map-approximation-of-zero-ℚ</a> <a id="6290" href="metric-spaces.rational-approximations-of-zero.html#6071" class="Bound">f</a><a id="6291" class="Symbol">)</a>
      <a id="6299" class="Symbol">(</a> <a id="6301" href="metric-spaces.rational-approximations-of-zero.html#2737" class="Function">is-approximation-of-zero-map-approximation-of-zero-ℚ</a> <a id="6354" href="metric-spaces.rational-approximations-of-zero.html#6071" class="Bound">f</a><a id="6355" class="Symbol">)</a>

  <a id="6360" href="metric-spaces.rational-approximations-of-zero.html#6360" class="Function">is-zero-limit-cauchy-approximation-of-zero-ℚ</a> <a id="6405" class="Symbol">:</a>
    <a id="6411" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2059" class="Function">is-limit-cauchy-approximation-Metric-Space</a>
      <a id="6460" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a>
      <a id="6481" href="metric-spaces.rational-approximations-of-zero.html#6111" class="Function">cauchy-approximation-of-zero-ℚ</a>
      <a id="6518" href="elementary-number-theory.rational-numbers.html#3520" class="Function">zero-ℚ</a>
  <a id="6527" href="metric-spaces.rational-approximations-of-zero.html#6360" class="Function">is-zero-limit-cauchy-approximation-of-zero-ℚ</a> <a id="6572" class="Symbol">=</a>
    <a id="6578" href="metric-spaces.rational-approximations-of-zero.html#5350" class="Function">is-zero-limit-is-approximation-of-zero-ℚ</a>
      <a id="6625" class="Symbol">(</a> <a id="6627" href="metric-spaces.rational-approximations-of-zero.html#2659" class="Function">map-approximation-of-zero-ℚ</a> <a id="6655" href="metric-spaces.rational-approximations-of-zero.html#6071" class="Bound">f</a><a id="6656" class="Symbol">)</a>
      <a id="6664" class="Symbol">(</a> <a id="6666" href="metric-spaces.rational-approximations-of-zero.html#2737" class="Function">is-approximation-of-zero-map-approximation-of-zero-ℚ</a> <a id="6719" href="metric-spaces.rational-approximations-of-zero.html#6071" class="Bound">f</a><a id="6720" class="Symbol">)</a>

  <a id="6725" href="metric-spaces.rational-approximations-of-zero.html#6725" class="Function">zero-limit-cauchy-approximation-of-zero-ℚ</a> <a id="6767" class="Symbol">:</a> <a id="6769" href="metric-spaces.rational-approximations-of-zero.html#2994" class="Function">zero-limit-cauchy-approximation-ℚ</a>
  <a id="6805" href="metric-spaces.rational-approximations-of-zero.html#6725" class="Function">zero-limit-cauchy-approximation-of-zero-ℚ</a> <a id="6847" class="Symbol">=</a>
    <a id="6853" href="metric-spaces.rational-approximations-of-zero.html#6111" class="Function">cauchy-approximation-of-zero-ℚ</a> <a id="6884" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="6890" href="metric-spaces.rational-approximations-of-zero.html#6360" class="Function">is-zero-limit-cauchy-approximation-of-zero-ℚ</a>

<a id="6936" class="Keyword">module</a> <a id="6943" href="metric-spaces.rational-approximations-of-zero.html#6943" class="Module">_</a>
  <a id="6947" class="Symbol">(</a> <a id="6949" href="metric-spaces.rational-approximations-of-zero.html#6949" class="Bound">f</a> <a id="6951" class="Symbol">:</a> <a id="6953" href="metric-spaces.rational-cauchy-approximations.html#1594" class="Function">cauchy-approximation-ℚ</a><a id="6975" class="Symbol">)</a>
  <a id="6979" class="Symbol">(</a> <a id="6981" href="metric-spaces.rational-approximations-of-zero.html#6981" class="Bound">L</a> <a id="6983" class="Symbol">:</a>
    <a id="6989" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2059" class="Function">is-limit-cauchy-approximation-Metric-Space</a>
      <a id="7038" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a>
      <a id="7059" href="metric-spaces.rational-approximations-of-zero.html#6949" class="Bound">f</a>
      <a id="7067" href="elementary-number-theory.rational-numbers.html#3520" class="Function">zero-ℚ</a><a id="7073" class="Symbol">)</a>
  <a id="7077" class="Keyword">where</a>

  <a id="7086" class="Keyword">abstract</a>
    <a id="7099" href="metric-spaces.rational-approximations-of-zero.html#7099" class="Function">is-approximation-is-zero-limit-cauchy-approximation-ℚ</a> <a id="7153" class="Symbol">:</a>
      <a id="7161" href="metric-spaces.rational-approximations-of-zero.html#2384" class="Function">is-approximation-of-zero-ℚ</a> <a id="7188" class="Symbol">(</a><a id="7189" href="metric-spaces.rational-cauchy-approximations.html#1705" class="Function">map-cauchy-approximation-ℚ</a> <a id="7216" href="metric-spaces.rational-approximations-of-zero.html#6949" class="Bound">f</a><a id="7217" class="Symbol">)</a>
    <a id="7223" href="metric-spaces.rational-approximations-of-zero.html#7099" class="Function">is-approximation-is-zero-limit-cauchy-approximation-ℚ</a> <a id="7277" href="metric-spaces.rational-approximations-of-zero.html#7277" class="Bound">ε</a> <a id="7279" class="Symbol">=</a>
      <a id="7287" href="foundation-core.transport-along-identifications.html#832" class="Function">tr</a>
        <a id="7298" class="Symbol">(</a> <a id="7300" class="Symbol">λ</a> <a id="7302" href="metric-spaces.rational-approximations-of-zero.html#7302" class="Bound">y</a> <a id="7304" class="Symbol">→</a> <a id="7306" href="elementary-number-theory.inequality-rational-numbers.html#2922" class="Function">leq-ℚ</a> <a id="7312" href="metric-spaces.rational-approximations-of-zero.html#7302" class="Bound">y</a> <a id="7314" class="Symbol">(</a><a id="7315" href="elementary-number-theory.positive-rational-numbers.html#4840" class="Function">rational-ℚ⁺</a> <a id="7327" href="metric-spaces.rational-approximations-of-zero.html#7277" class="Bound">ε</a><a id="7328" class="Symbol">))</a>
        <a id="7339" class="Symbol">(</a> <a id="7341" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
          <a id="7354" class="Symbol">(</a> <a id="7356" href="elementary-number-theory.nonnegative-rational-numbers.html#2618" class="Function">rational-ℚ⁰⁺</a><a id="7368" class="Symbol">)</a>
          <a id="7380" class="Symbol">(</a> <a id="7382" href="elementary-number-theory.distance-rational-numbers.html#2714" class="Function">right-zero-law-dist-ℚ</a> <a id="7404" class="Symbol">(</a><a id="7405" href="metric-spaces.rational-cauchy-approximations.html#1705" class="Function">map-cauchy-approximation-ℚ</a> <a id="7432" href="metric-spaces.rational-approximations-of-zero.html#6949" class="Bound">f</a> <a id="7434" href="metric-spaces.rational-approximations-of-zero.html#7277" class="Bound">ε</a><a id="7435" class="Symbol">)))</a>
        <a id="7447" class="Symbol">(</a> <a id="7449" href="metric-spaces.metric-space-of-rational-numbers.html#7346" class="Function">leq-dist-neighborhood-ℚ</a>
          <a id="7483" class="Symbol">(</a> <a id="7485" href="metric-spaces.rational-approximations-of-zero.html#7277" class="Bound">ε</a><a id="7486" class="Symbol">)</a>
          <a id="7498" class="Symbol">(</a> <a id="7500" href="metric-spaces.rational-cauchy-approximations.html#1705" class="Function">map-cauchy-approximation-ℚ</a> <a id="7527" href="metric-spaces.rational-approximations-of-zero.html#6949" class="Bound">f</a> <a id="7529" href="metric-spaces.rational-approximations-of-zero.html#7277" class="Bound">ε</a><a id="7530" class="Symbol">)</a>
          <a id="7542" class="Symbol">(</a> <a id="7544" href="elementary-number-theory.rational-numbers.html#3520" class="Function">zero-ℚ</a><a id="7550" class="Symbol">)</a>
          <a id="7562" class="Symbol">(</a> <a id="7564" href="metric-spaces.metric-spaces.html#8643" class="Function">saturated-neighborhood-Metric-Space</a>
            <a id="7612" class="Symbol">(</a> <a id="7614" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a><a id="7628" class="Symbol">)</a>
            <a id="7642" class="Symbol">(</a> <a id="7644" href="metric-spaces.rational-approximations-of-zero.html#7277" class="Bound">ε</a><a id="7645" class="Symbol">)</a>
            <a id="7659" class="Symbol">(</a> <a id="7661" href="metric-spaces.rational-cauchy-approximations.html#1705" class="Function">map-cauchy-approximation-ℚ</a> <a id="7688" href="metric-spaces.rational-approximations-of-zero.html#6949" class="Bound">f</a> <a id="7690" href="metric-spaces.rational-approximations-of-zero.html#7277" class="Bound">ε</a><a id="7691" class="Symbol">)</a>
            <a id="7705" class="Symbol">(</a> <a id="7707" href="elementary-number-theory.rational-numbers.html#3520" class="Function">zero-ℚ</a><a id="7713" class="Symbol">)</a>
            <a id="7727" class="Symbol">(</a> <a id="7729" href="metric-spaces.rational-approximations-of-zero.html#6981" class="Bound">L</a> <a id="7731" href="metric-spaces.rational-approximations-of-zero.html#7277" class="Bound">ε</a><a id="7732" class="Symbol">)))</a>

  <a id="7739" href="metric-spaces.rational-approximations-of-zero.html#7739" class="Function">approximation-of-zero-is-zero-limit-cauchy-approximation-ℚ</a> <a id="7798" class="Symbol">:</a>
    <a id="7804" href="metric-spaces.rational-approximations-of-zero.html#2500" class="Function">approximation-of-zero-ℚ</a>
  <a id="7830" href="metric-spaces.rational-approximations-of-zero.html#7739" class="Function">approximation-of-zero-is-zero-limit-cauchy-approximation-ℚ</a> <a id="7889" class="Symbol">=</a>
    <a id="7895" class="Symbol">(</a> <a id="7897" href="metric-spaces.rational-cauchy-approximations.html#1705" class="Function">map-cauchy-approximation-ℚ</a> <a id="7924" href="metric-spaces.rational-approximations-of-zero.html#6949" class="Bound">f</a><a id="7925" class="Symbol">)</a> <a id="7927" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="7933" class="Symbol">(</a> <a id="7935" href="metric-spaces.rational-approximations-of-zero.html#7099" class="Function">is-approximation-is-zero-limit-cauchy-approximation-ℚ</a><a id="7988" class="Symbol">)</a>

<a id="approximation-of-zero-limit-cauchy-approximation-ℚ"></a><a id="7991" href="metric-spaces.rational-approximations-of-zero.html#7991" class="Function">approximation-of-zero-limit-cauchy-approximation-ℚ</a> <a id="8042" class="Symbol">:</a>
  <a id="8046" href="metric-spaces.rational-approximations-of-zero.html#2994" class="Function">zero-limit-cauchy-approximation-ℚ</a> <a id="8080" class="Symbol">→</a> <a id="8082" href="metric-spaces.rational-approximations-of-zero.html#2500" class="Function">approximation-of-zero-ℚ</a>
<a id="8106" href="metric-spaces.rational-approximations-of-zero.html#7991" class="Function">approximation-of-zero-limit-cauchy-approximation-ℚ</a> <a id="8157" class="Symbol">=</a>
  <a id="8161" href="foundation.dependent-pair-types.html#1097" class="Function">rec-Σ</a> <a id="8167" href="metric-spaces.rational-approximations-of-zero.html#7739" class="Function">approximation-of-zero-is-zero-limit-cauchy-approximation-ℚ</a>

<a id="section-zero-limit-cauchy-approximation-of-zero-ℚ"></a><a id="8227" href="metric-spaces.rational-approximations-of-zero.html#8227" class="Function">section-zero-limit-cauchy-approximation-of-zero-ℚ</a> <a id="8277" class="Symbol">:</a>
  <a id="8281" href="foundation-core.sections.html#1373" class="Function">section</a> <a id="8289" href="metric-spaces.rational-approximations-of-zero.html#6725" class="Function">zero-limit-cauchy-approximation-of-zero-ℚ</a>
<a id="8331" href="metric-spaces.rational-approximations-of-zero.html#8227" class="Function">section-zero-limit-cauchy-approximation-of-zero-ℚ</a> <a id="8381" class="Symbol">=</a>
  <a id="8385" class="Symbol">(</a> <a id="8387" href="metric-spaces.rational-approximations-of-zero.html#7991" class="Function">approximation-of-zero-limit-cauchy-approximation-ℚ</a><a id="8437" class="Symbol">)</a> <a id="8439" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
  <a id="8443" class="Symbol">(</a> <a id="8445" class="Symbol">λ</a> <a id="8447" href="metric-spaces.rational-approximations-of-zero.html#8447" class="Bound">f</a> <a id="8449" class="Symbol">→</a>
    <a id="8455" href="foundation-core.subtypes.html#3976" class="Function">eq-type-subtype</a>
      <a id="8477" class="Symbol">(</a> <a id="8479" class="Symbol">λ</a> <a id="8481" href="metric-spaces.rational-approximations-of-zero.html#8481" class="Bound">h</a> <a id="8483" class="Symbol">→</a>
        <a id="8493" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#1814" class="Function">is-limit-cauchy-approximation-prop-Metric-Space</a>
          <a id="8551" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a>
          <a id="8576" href="metric-spaces.rational-approximations-of-zero.html#8481" class="Bound">h</a>
          <a id="8588" href="elementary-number-theory.rational-numbers.html#3520" class="Function">zero-ℚ</a><a id="8594" class="Symbol">)</a>
      <a id="8602" class="Symbol">(</a> <a id="8604" href="foundation-core.subtypes.html#3976" class="Function">eq-type-subtype</a>
        <a id="8628" class="Symbol">(</a> <a id="8630" href="metric-spaces.cauchy-approximations-metric-spaces.html#1554" class="Function">is-cauchy-approximation-prop-Metric-Space</a> <a id="8672" href="metric-spaces.metric-space-of-rational-numbers.html#6954" class="Function">metric-space-ℚ</a><a id="8686" class="Symbol">)</a>
        <a id="8696" class="Symbol">(</a> <a id="8698" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="8702" class="Symbol">)))</a>

<a id="retraction-zero-limit-cauchy-approximation-of-zero-ℚ"></a><a id="8707" href="metric-spaces.rational-approximations-of-zero.html#8707" class="Function">retraction-zero-limit-cauchy-approximation-of-zero-ℚ</a> <a id="8760" class="Symbol">:</a>
  <a id="8764" href="foundation-core.retractions.html#874" class="Function">retraction</a> <a id="8775" href="metric-spaces.rational-approximations-of-zero.html#6725" class="Function">zero-limit-cauchy-approximation-of-zero-ℚ</a>
<a id="8817" href="metric-spaces.rational-approximations-of-zero.html#8707" class="Function">retraction-zero-limit-cauchy-approximation-of-zero-ℚ</a> <a id="8870" class="Symbol">=</a>
  <a id="8874" class="Symbol">(</a> <a id="8876" href="metric-spaces.rational-approximations-of-zero.html#7991" class="Function">approximation-of-zero-limit-cauchy-approximation-ℚ</a><a id="8926" class="Symbol">)</a> <a id="8928" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
  <a id="8932" class="Symbol">(</a> <a id="8934" class="Symbol">λ</a> <a id="8936" href="metric-spaces.rational-approximations-of-zero.html#8936" class="Bound">f</a> <a id="8938" class="Symbol">→</a>
    <a id="8944" href="foundation-core.subtypes.html#3976" class="Function">eq-type-subtype</a>
      <a id="8966" class="Symbol">(</a> <a id="8968" href="metric-spaces.rational-approximations-of-zero.html#2212" class="Function">subtype-approximation-of-zero-ℚ</a><a id="8999" class="Symbol">)</a>
      <a id="9007" class="Symbol">(</a> <a id="9009" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="9013" class="Symbol">))</a>

<a id="is-equiv-zero-limit-cauchy-approximation-of-zero-ℚ"></a><a id="9017" href="metric-spaces.rational-approximations-of-zero.html#9017" class="Function">is-equiv-zero-limit-cauchy-approximation-of-zero-ℚ</a> <a id="9068" class="Symbol">:</a>
  <a id="9072" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="9081" href="metric-spaces.rational-approximations-of-zero.html#6725" class="Function">zero-limit-cauchy-approximation-of-zero-ℚ</a>
<a id="9123" href="metric-spaces.rational-approximations-of-zero.html#9017" class="Function">is-equiv-zero-limit-cauchy-approximation-of-zero-ℚ</a> <a id="9174" class="Symbol">=</a>
  <a id="9178" href="metric-spaces.rational-approximations-of-zero.html#8227" class="Function">section-zero-limit-cauchy-approximation-of-zero-ℚ</a> <a id="9228" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
  <a id="9232" href="metric-spaces.rational-approximations-of-zero.html#8707" class="Function">retraction-zero-limit-cauchy-approximation-of-zero-ℚ</a>

<a id="equiv-zero-limit-cacuhy-approximation-of-zero-ℚ"></a><a id="9286" href="metric-spaces.rational-approximations-of-zero.html#9286" class="Function">equiv-zero-limit-cacuhy-approximation-of-zero-ℚ</a> <a id="9334" class="Symbol">:</a>
  <a id="9338" href="metric-spaces.rational-approximations-of-zero.html#2500" class="Function">approximation-of-zero-ℚ</a> <a id="9362" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="9364" href="metric-spaces.rational-approximations-of-zero.html#2994" class="Function">zero-limit-cauchy-approximation-ℚ</a>
<a id="9398" href="metric-spaces.rational-approximations-of-zero.html#9286" class="Function">equiv-zero-limit-cacuhy-approximation-of-zero-ℚ</a> <a id="9446" class="Symbol">=</a>
  <a id="9450" href="metric-spaces.rational-approximations-of-zero.html#6725" class="Function">zero-limit-cauchy-approximation-of-zero-ℚ</a> <a id="9492" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
  <a id="9496" href="metric-spaces.rational-approximations-of-zero.html#9017" class="Function">is-equiv-zero-limit-cauchy-approximation-of-zero-ℚ</a>
</pre>