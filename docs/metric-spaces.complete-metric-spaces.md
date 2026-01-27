# Complete metric spaces

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="metric-spaces.complete-metric-spaces.html" class="Module">metric-spaces.complete-metric-spaces</a> <a id="79" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="135" class="Keyword">open</a> <a id="140" class="Keyword">import</a> <a id="147" href="elementary-number-theory.positive-rational-numbers.html" class="Module">elementary-number-theory.positive-rational-numbers</a>

<a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="239" class="Keyword">open</a> <a id="244" class="Keyword">import</a> <a id="251" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="319" class="Keyword">open</a> <a id="324" class="Keyword">import</a> <a id="331" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="357" class="Keyword">open</a> <a id="362" class="Keyword">import</a> <a id="369" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="393" class="Keyword">open</a> <a id="398" class="Keyword">import</a> <a id="405" href="foundation.retractions.html" class="Module">foundation.retractions</a>
<a id="428" class="Keyword">open</a> <a id="433" class="Keyword">import</a> <a id="440" href="foundation.sections.html" class="Module">foundation.sections</a>
<a id="460" class="Keyword">open</a> <a id="465" class="Keyword">import</a> <a id="472" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="492" class="Keyword">open</a> <a id="497" class="Keyword">import</a> <a id="504" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="532" class="Keyword">open</a> <a id="537" class="Keyword">import</a> <a id="544" href="metric-spaces.cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.cauchy-approximations-metric-spaces</a>
<a id="594" class="Keyword">open</a> <a id="599" class="Keyword">import</a> <a id="606" href="metric-spaces.convergent-cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.convergent-cauchy-approximations-metric-spaces</a>
<a id="667" class="Keyword">open</a> <a id="672" class="Keyword">import</a> <a id="679" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.limits-of-cauchy-approximations-metric-spaces</a>
<a id="739" class="Keyword">open</a> <a id="744" class="Keyword">import</a> <a id="751" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
</pre>
</details>

## Idea

A [metric space](metric-spaces.metric-spaces.md) is
{{#concept "complete" Disambiguation="metric space" Agda=is-complete-Metric-Space WD="complete metric space" WDID=Q848569}}
if all its
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md)
are
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces.md).

## Definitions

### The property of being a complete metric space

<pre class="Agda"><a id="1229" class="Keyword">module</a> <a id="1236" href="metric-spaces.complete-metric-spaces.html#1236" class="Module">_</a>
  <a id="1240" class="Symbol">{</a><a id="1241" href="metric-spaces.complete-metric-spaces.html#1241" class="Bound">l1</a> <a id="1244" href="metric-spaces.complete-metric-spaces.html#1244" class="Bound">l2</a> <a id="1247" class="Symbol">:</a> <a id="1249" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1254" class="Symbol">}</a> <a id="1256" class="Symbol">(</a><a id="1257" href="metric-spaces.complete-metric-spaces.html#1257" class="Bound">A</a> <a id="1259" class="Symbol">:</a> <a id="1261" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1274" href="metric-spaces.complete-metric-spaces.html#1241" class="Bound">l1</a> <a id="1277" href="metric-spaces.complete-metric-spaces.html#1244" class="Bound">l2</a><a id="1279" class="Symbol">)</a>
  <a id="1283" class="Keyword">where</a>

  <a id="1292" href="metric-spaces.complete-metric-spaces.html#1292" class="Function">is-complete-prop-Metric-Space</a> <a id="1322" class="Symbol">:</a> <a id="1324" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1329" class="Symbol">(</a><a id="1330" href="metric-spaces.complete-metric-spaces.html#1241" class="Bound">l1</a> <a id="1333" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1335" href="metric-spaces.complete-metric-spaces.html#1244" class="Bound">l2</a><a id="1337" class="Symbol">)</a>
  <a id="1341" href="metric-spaces.complete-metric-spaces.html#1292" class="Function">is-complete-prop-Metric-Space</a> <a id="1371" class="Symbol">=</a>
    <a id="1377" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="1390" class="Symbol">(</a> <a id="1392" href="metric-spaces.cauchy-approximations-metric-spaces.html#1957" class="Function">cauchy-approximation-Metric-Space</a> <a id="1426" href="metric-spaces.complete-metric-spaces.html#1257" class="Bound">A</a><a id="1427" class="Symbol">)</a>
      <a id="1435" class="Symbol">(</a> <a id="1437" href="metric-spaces.convergent-cauchy-approximations-metric-spaces.html#2972" class="Function">is-convergent-prop-cauchy-approximation-Metric-Space</a> <a id="1490" href="metric-spaces.complete-metric-spaces.html#1257" class="Bound">A</a><a id="1491" class="Symbol">)</a>

  <a id="1496" href="metric-spaces.complete-metric-spaces.html#1496" class="Function">is-complete-Metric-Space</a> <a id="1521" class="Symbol">:</a> <a id="1523" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1526" class="Symbol">(</a><a id="1527" href="metric-spaces.complete-metric-spaces.html#1241" class="Bound">l1</a> <a id="1530" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1532" href="metric-spaces.complete-metric-spaces.html#1244" class="Bound">l2</a><a id="1534" class="Symbol">)</a>
  <a id="1538" href="metric-spaces.complete-metric-spaces.html#1496" class="Function">is-complete-Metric-Space</a> <a id="1563" class="Symbol">=</a> <a id="1565" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1575" href="metric-spaces.complete-metric-spaces.html#1292" class="Function">is-complete-prop-Metric-Space</a>

  <a id="1608" href="metric-spaces.complete-metric-spaces.html#1608" class="Function">is-prop-is-complete-Metric-Space</a> <a id="1641" class="Symbol">:</a> <a id="1643" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1651" href="metric-spaces.complete-metric-spaces.html#1496" class="Function">is-complete-Metric-Space</a>
  <a id="1678" href="metric-spaces.complete-metric-spaces.html#1608" class="Function">is-prop-is-complete-Metric-Space</a> <a id="1711" class="Symbol">=</a>
    <a id="1717" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1735" href="metric-spaces.complete-metric-spaces.html#1292" class="Function">is-complete-prop-Metric-Space</a>
</pre>
### The type of complete metric spaces

<pre class="Agda"><a id="1818" class="Keyword">module</a> <a id="1825" href="metric-spaces.complete-metric-spaces.html#1825" class="Module">_</a>
  <a id="1829" class="Symbol">(</a><a id="1830" href="metric-spaces.complete-metric-spaces.html#1830" class="Bound">l1</a> <a id="1833" href="metric-spaces.complete-metric-spaces.html#1833" class="Bound">l2</a> <a id="1836" class="Symbol">:</a> <a id="1838" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1843" class="Symbol">)</a>
  <a id="1847" class="Keyword">where</a>

  <a id="1856" href="metric-spaces.complete-metric-spaces.html#1856" class="Function">Complete-Metric-Space</a> <a id="1878" class="Symbol">:</a> <a id="1880" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1883" class="Symbol">(</a><a id="1884" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1889" href="metric-spaces.complete-metric-spaces.html#1830" class="Bound">l1</a> <a id="1892" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1894" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1899" href="metric-spaces.complete-metric-spaces.html#1833" class="Bound">l2</a><a id="1901" class="Symbol">)</a>
  <a id="1905" href="metric-spaces.complete-metric-spaces.html#1856" class="Function">Complete-Metric-Space</a> <a id="1927" class="Symbol">=</a>
    <a id="1933" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="1946" class="Symbol">(</a><a id="1947" href="metric-spaces.complete-metric-spaces.html#1292" class="Function">is-complete-prop-Metric-Space</a> <a id="1977" class="Symbol">{</a><a id="1978" href="metric-spaces.complete-metric-spaces.html#1830" class="Bound">l1</a><a id="1980" class="Symbol">}</a> <a id="1982" class="Symbol">{</a><a id="1983" href="metric-spaces.complete-metric-spaces.html#1833" class="Bound">l2</a><a id="1985" class="Symbol">})</a>
</pre>
<pre class="Agda"><a id="2001" class="Keyword">module</a> <a id="2008" href="metric-spaces.complete-metric-spaces.html#2008" class="Module">_</a>
  <a id="2012" class="Symbol">{</a><a id="2013" href="metric-spaces.complete-metric-spaces.html#2013" class="Bound">l1</a> <a id="2016" href="metric-spaces.complete-metric-spaces.html#2016" class="Bound">l2</a> <a id="2019" class="Symbol">:</a> <a id="2021" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2026" class="Symbol">}</a>
  <a id="2030" class="Symbol">(</a><a id="2031" href="metric-spaces.complete-metric-spaces.html#2031" class="Bound">A</a> <a id="2033" class="Symbol">:</a> <a id="2035" href="metric-spaces.complete-metric-spaces.html#1856" class="Function">Complete-Metric-Space</a> <a id="2057" href="metric-spaces.complete-metric-spaces.html#2013" class="Bound">l1</a> <a id="2060" href="metric-spaces.complete-metric-spaces.html#2016" class="Bound">l2</a><a id="2062" class="Symbol">)</a>
  <a id="2066" class="Keyword">where</a>

  <a id="2075" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="2110" class="Symbol">:</a> <a id="2112" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="2125" href="metric-spaces.complete-metric-spaces.html#2013" class="Bound">l1</a> <a id="2128" href="metric-spaces.complete-metric-spaces.html#2016" class="Bound">l2</a>
  <a id="2133" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="2168" class="Symbol">=</a> <a id="2170" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2174" href="metric-spaces.complete-metric-spaces.html#2031" class="Bound">A</a>

  <a id="2179" href="metric-spaces.complete-metric-spaces.html#2179" class="Function">type-Complete-Metric-Space</a> <a id="2206" class="Symbol">:</a> <a id="2208" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2211" href="metric-spaces.complete-metric-spaces.html#2013" class="Bound">l1</a>
  <a id="2216" href="metric-spaces.complete-metric-spaces.html#2179" class="Function">type-Complete-Metric-Space</a> <a id="2243" class="Symbol">=</a>
    <a id="2249" href="metric-spaces.metric-spaces.html#5090" class="Function">type-Metric-Space</a> <a id="2267" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a>

  <a id="2305" href="metric-spaces.complete-metric-spaces.html#2305" class="Function">is-complete-metric-space-Complete-Metric-Space</a> <a id="2352" class="Symbol">:</a>
    <a id="2358" href="metric-spaces.complete-metric-spaces.html#1496" class="Function">is-complete-Metric-Space</a> <a id="2383" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a>
  <a id="2420" href="metric-spaces.complete-metric-spaces.html#2305" class="Function">is-complete-metric-space-Complete-Metric-Space</a> <a id="2467" class="Symbol">=</a> <a id="2469" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2473" href="metric-spaces.complete-metric-spaces.html#2031" class="Bound">A</a>

  <a id="2478" href="metric-spaces.complete-metric-spaces.html#2478" class="Function">neighborhood-Complete-Metric-Space</a> <a id="2513" class="Symbol">:</a>
    <a id="2519" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a> <a id="2522" class="Symbol">→</a> <a id="2524" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="2533" href="metric-spaces.complete-metric-spaces.html#2016" class="Bound">l2</a> <a id="2536" href="metric-spaces.complete-metric-spaces.html#2179" class="Function">type-Complete-Metric-Space</a>
  <a id="2565" href="metric-spaces.complete-metric-spaces.html#2478" class="Function">neighborhood-Complete-Metric-Space</a> <a id="2600" class="Symbol">=</a>
    <a id="2606" href="metric-spaces.metric-spaces.html#5726" class="Function">neighborhood-Metric-Space</a> <a id="2632" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a>
</pre>
### The equivalence between Cauchy approximations and convergent Cauchy approximations in a complete metric space

<pre class="Agda"><a id="2795" class="Keyword">module</a> <a id="2802" href="metric-spaces.complete-metric-spaces.html#2802" class="Module">_</a>
  <a id="2806" class="Symbol">{</a><a id="2807" href="metric-spaces.complete-metric-spaces.html#2807" class="Bound">l1</a> <a id="2810" href="metric-spaces.complete-metric-spaces.html#2810" class="Bound">l2</a> <a id="2813" class="Symbol">:</a> <a id="2815" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2820" class="Symbol">}</a>
  <a id="2824" class="Symbol">(</a><a id="2825" href="metric-spaces.complete-metric-spaces.html#2825" class="Bound">A</a> <a id="2827" class="Symbol">:</a> <a id="2829" href="metric-spaces.complete-metric-spaces.html#1856" class="Function">Complete-Metric-Space</a> <a id="2851" href="metric-spaces.complete-metric-spaces.html#2807" class="Bound">l1</a> <a id="2854" href="metric-spaces.complete-metric-spaces.html#2810" class="Bound">l2</a><a id="2856" class="Symbol">)</a>
  <a id="2860" class="Keyword">where</a>

  <a id="2869" href="metric-spaces.complete-metric-spaces.html#2869" class="Function">convergent-cauchy-approximation-Complete-Metric-Space</a> <a id="2923" class="Symbol">:</a>
    <a id="2929" href="metric-spaces.cauchy-approximations-metric-spaces.html#1957" class="Function">cauchy-approximation-Metric-Space</a>
      <a id="2969" class="Symbol">(</a> <a id="2971" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="3006" href="metric-spaces.complete-metric-spaces.html#2825" class="Bound">A</a><a id="3007" class="Symbol">)</a> <a id="3009" class="Symbol">→</a>
    <a id="3015" href="metric-spaces.convergent-cauchy-approximations-metric-spaces.html#3357" class="Function">convergent-cauchy-approximation-Metric-Space</a>
      <a id="3066" class="Symbol">(</a> <a id="3068" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="3103" href="metric-spaces.complete-metric-spaces.html#2825" class="Bound">A</a><a id="3104" class="Symbol">)</a>
  <a id="3108" href="metric-spaces.complete-metric-spaces.html#2869" class="Function">convergent-cauchy-approximation-Complete-Metric-Space</a> <a id="3162" href="metric-spaces.complete-metric-spaces.html#3162" class="Bound">u</a> <a id="3164" class="Symbol">=</a>
    <a id="3170" class="Symbol">(</a> <a id="3172" href="metric-spaces.complete-metric-spaces.html#3162" class="Bound">u</a> <a id="3174" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3176" href="metric-spaces.complete-metric-spaces.html#2305" class="Function">is-complete-metric-space-Complete-Metric-Space</a> <a id="3223" href="metric-spaces.complete-metric-spaces.html#2825" class="Bound">A</a> <a id="3225" href="metric-spaces.complete-metric-spaces.html#3162" class="Bound">u</a><a id="3226" class="Symbol">)</a>

  <a id="3231" href="metric-spaces.complete-metric-spaces.html#3231" class="Function">is-section-convergent-cauchy-approximation-Complete-Metric-Space</a> <a id="3296" class="Symbol">:</a>
    <a id="3302" href="foundation-core.sections.html#1194" class="Function">is-section</a>
      <a id="3319" class="Symbol">(</a> <a id="3321" href="metric-spaces.complete-metric-spaces.html#2869" class="Function">convergent-cauchy-approximation-Complete-Metric-Space</a><a id="3374" class="Symbol">)</a>
      <a id="3382" class="Symbol">(</a> <a id="3384" href="foundation-core.subtypes.html#1842" class="Function">inclusion-subtype</a>
        <a id="3410" class="Symbol">(</a> <a id="3412" href="metric-spaces.convergent-cauchy-approximations-metric-spaces.html#2972" class="Function">is-convergent-prop-cauchy-approximation-Metric-Space</a>
          <a id="3475" class="Symbol">(</a> <a id="3477" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="3512" href="metric-spaces.complete-metric-spaces.html#2825" class="Bound">A</a><a id="3513" class="Symbol">)))</a>
  <a id="3519" href="metric-spaces.complete-metric-spaces.html#3231" class="Function">is-section-convergent-cauchy-approximation-Complete-Metric-Space</a> <a id="3584" href="metric-spaces.complete-metric-spaces.html#3584" class="Bound">u</a> <a id="3586" class="Symbol">=</a>
    <a id="3592" href="foundation-core.subtypes.html#3976" class="Function">eq-type-subtype</a>
      <a id="3614" class="Symbol">(</a> <a id="3616" href="metric-spaces.convergent-cauchy-approximations-metric-spaces.html#2972" class="Function">is-convergent-prop-cauchy-approximation-Metric-Space</a>
        <a id="3677" class="Symbol">(</a> <a id="3679" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="3714" href="metric-spaces.complete-metric-spaces.html#2825" class="Bound">A</a><a id="3715" class="Symbol">))</a>
      <a id="3724" class="Symbol">(</a> <a id="3726" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="3730" class="Symbol">)</a>

  <a id="3735" href="metric-spaces.complete-metric-spaces.html#3735" class="Function">is-retraction-convergent-cauchy-approximation-Metric-Space</a> <a id="3794" class="Symbol">:</a>
    <a id="3800" href="foundation-core.retractions.html#790" class="Function">is-retraction</a>
      <a id="3820" class="Symbol">(</a> <a id="3822" href="metric-spaces.complete-metric-spaces.html#2869" class="Function">convergent-cauchy-approximation-Complete-Metric-Space</a><a id="3875" class="Symbol">)</a>
      <a id="3883" class="Symbol">(</a> <a id="3885" href="foundation-core.subtypes.html#1842" class="Function">inclusion-subtype</a>
        <a id="3911" class="Symbol">(</a> <a id="3913" href="metric-spaces.convergent-cauchy-approximations-metric-spaces.html#2972" class="Function">is-convergent-prop-cauchy-approximation-Metric-Space</a>
          <a id="3976" class="Symbol">(</a> <a id="3978" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="4013" href="metric-spaces.complete-metric-spaces.html#2825" class="Bound">A</a><a id="4014" class="Symbol">)))</a>
  <a id="4020" href="metric-spaces.complete-metric-spaces.html#3735" class="Function">is-retraction-convergent-cauchy-approximation-Metric-Space</a> <a id="4079" href="metric-spaces.complete-metric-spaces.html#4079" class="Bound">u</a> <a id="4081" class="Symbol">=</a> <a id="4083" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

  <a id="4091" href="metric-spaces.complete-metric-spaces.html#4091" class="Function">is-equiv-convergent-cauchy-approximation-Complete-Metric-Space</a> <a id="4154" class="Symbol">:</a>
    <a id="4160" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="4169" href="metric-spaces.complete-metric-spaces.html#2869" class="Function">convergent-cauchy-approximation-Complete-Metric-Space</a>
  <a id="4225" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4229" href="metric-spaces.complete-metric-spaces.html#4091" class="Function">is-equiv-convergent-cauchy-approximation-Complete-Metric-Space</a> <a id="4292" class="Symbol">=</a>
    <a id="4298" class="Symbol">(</a> <a id="4300" href="foundation-core.subtypes.html#1842" class="Function">inclusion-subtype</a>
      <a id="4324" class="Symbol">(</a> <a id="4326" href="metric-spaces.convergent-cauchy-approximations-metric-spaces.html#2972" class="Function">is-convergent-prop-cauchy-approximation-Metric-Space</a>
        <a id="4387" class="Symbol">(</a> <a id="4389" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="4424" href="metric-spaces.complete-metric-spaces.html#2825" class="Bound">A</a><a id="4425" class="Symbol">)))</a> <a id="4429" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="4435" class="Symbol">(</a> <a id="4437" href="metric-spaces.complete-metric-spaces.html#3231" class="Function">is-section-convergent-cauchy-approximation-Complete-Metric-Space</a><a id="4501" class="Symbol">)</a>
  <a id="4505" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4509" href="metric-spaces.complete-metric-spaces.html#4091" class="Function">is-equiv-convergent-cauchy-approximation-Complete-Metric-Space</a> <a id="4572" class="Symbol">=</a>
    <a id="4578" class="Symbol">(</a> <a id="4580" href="foundation-core.subtypes.html#1842" class="Function">inclusion-subtype</a>
      <a id="4604" class="Symbol">(</a> <a id="4606" href="metric-spaces.convergent-cauchy-approximations-metric-spaces.html#2972" class="Function">is-convergent-prop-cauchy-approximation-Metric-Space</a>
        <a id="4667" class="Symbol">(</a> <a id="4669" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="4704" href="metric-spaces.complete-metric-spaces.html#2825" class="Bound">A</a><a id="4705" class="Symbol">)))</a> <a id="4709" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="4715" class="Symbol">(</a> <a id="4717" href="metric-spaces.complete-metric-spaces.html#3735" class="Function">is-retraction-convergent-cauchy-approximation-Metric-Space</a><a id="4775" class="Symbol">)</a>
</pre>
### The limit of a Cauchy approximation in a complete metric space

<pre class="Agda"><a id="4858" class="Keyword">module</a> <a id="4865" href="metric-spaces.complete-metric-spaces.html#4865" class="Module">_</a>
  <a id="4869" class="Symbol">{</a> <a id="4871" href="metric-spaces.complete-metric-spaces.html#4871" class="Bound">l1</a> <a id="4874" href="metric-spaces.complete-metric-spaces.html#4874" class="Bound">l2</a> <a id="4877" class="Symbol">:</a> <a id="4879" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4884" class="Symbol">}</a>
  <a id="4888" class="Symbol">(</a> <a id="4890" href="metric-spaces.complete-metric-spaces.html#4890" class="Bound">A</a> <a id="4892" class="Symbol">:</a> <a id="4894" href="metric-spaces.complete-metric-spaces.html#1856" class="Function">Complete-Metric-Space</a> <a id="4916" href="metric-spaces.complete-metric-spaces.html#4871" class="Bound">l1</a> <a id="4919" href="metric-spaces.complete-metric-spaces.html#4874" class="Bound">l2</a><a id="4921" class="Symbol">)</a>
  <a id="4925" class="Symbol">(</a> <a id="4927" href="metric-spaces.complete-metric-spaces.html#4927" class="Bound">u</a> <a id="4929" class="Symbol">:</a> <a id="4931" href="metric-spaces.cauchy-approximations-metric-spaces.html#1957" class="Function">cauchy-approximation-Metric-Space</a>
    <a id="4969" class="Symbol">(</a> <a id="4971" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="5006" href="metric-spaces.complete-metric-spaces.html#4890" class="Bound">A</a><a id="5007" class="Symbol">))</a>
  <a id="5012" class="Keyword">where</a>

  <a id="5021" href="metric-spaces.complete-metric-spaces.html#5021" class="Function">limit-cauchy-approximation-Complete-Metric-Space</a> <a id="5070" class="Symbol">:</a>
    <a id="5076" href="metric-spaces.complete-metric-spaces.html#2179" class="Function">type-Complete-Metric-Space</a> <a id="5103" href="metric-spaces.complete-metric-spaces.html#4890" class="Bound">A</a>
  <a id="5107" href="metric-spaces.complete-metric-spaces.html#5021" class="Function">limit-cauchy-approximation-Complete-Metric-Space</a> <a id="5156" class="Symbol">=</a>
    <a id="5162" href="metric-spaces.convergent-cauchy-approximations-metric-spaces.html#4584" class="Function">limit-convergent-cauchy-approximation-Metric-Space</a>
      <a id="5219" class="Symbol">(</a> <a id="5221" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="5256" href="metric-spaces.complete-metric-spaces.html#4890" class="Bound">A</a><a id="5257" class="Symbol">)</a>
      <a id="5265" class="Symbol">(</a> <a id="5267" href="metric-spaces.complete-metric-spaces.html#2869" class="Function">convergent-cauchy-approximation-Complete-Metric-Space</a> <a id="5321" href="metric-spaces.complete-metric-spaces.html#4890" class="Bound">A</a> <a id="5323" href="metric-spaces.complete-metric-spaces.html#4927" class="Bound">u</a><a id="5324" class="Symbol">)</a>

  <a id="5329" href="metric-spaces.complete-metric-spaces.html#5329" class="Function">is-limit-limit-cauchy-approximation-Complete-Metric-Space</a> <a id="5387" class="Symbol">:</a>
    <a id="5393" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2059" class="Function">is-limit-cauchy-approximation-Metric-Space</a>
      <a id="5442" class="Symbol">(</a> <a id="5444" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="5479" href="metric-spaces.complete-metric-spaces.html#4890" class="Bound">A</a><a id="5480" class="Symbol">)</a>
      <a id="5488" class="Symbol">(</a> <a id="5490" href="metric-spaces.complete-metric-spaces.html#4927" class="Bound">u</a><a id="5491" class="Symbol">)</a>
      <a id="5499" class="Symbol">(</a> <a id="5501" href="metric-spaces.complete-metric-spaces.html#5021" class="Function">limit-cauchy-approximation-Complete-Metric-Space</a><a id="5549" class="Symbol">)</a>
  <a id="5553" href="metric-spaces.complete-metric-spaces.html#5329" class="Function">is-limit-limit-cauchy-approximation-Complete-Metric-Space</a> <a id="5611" class="Symbol">=</a>
    <a id="5617" href="metric-spaces.convergent-cauchy-approximations-metric-spaces.html#4731" class="Function">is-limit-limit-convergent-cauchy-approximation-Metric-Space</a>
      <a id="5683" class="Symbol">(</a> <a id="5685" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="5720" href="metric-spaces.complete-metric-spaces.html#4890" class="Bound">A</a><a id="5721" class="Symbol">)</a>
      <a id="5729" class="Symbol">(</a> <a id="5731" href="metric-spaces.complete-metric-spaces.html#2869" class="Function">convergent-cauchy-approximation-Complete-Metric-Space</a> <a id="5785" href="metric-spaces.complete-metric-spaces.html#4890" class="Bound">A</a> <a id="5787" href="metric-spaces.complete-metric-spaces.html#4927" class="Bound">u</a><a id="5788" class="Symbol">)</a>
</pre>
### Saturation of the limit

<pre class="Agda"><a id="5832" class="Keyword">module</a> <a id="5839" href="metric-spaces.complete-metric-spaces.html#5839" class="Module">_</a>
  <a id="5843" class="Symbol">{</a><a id="5844" href="metric-spaces.complete-metric-spaces.html#5844" class="Bound">l1</a> <a id="5847" href="metric-spaces.complete-metric-spaces.html#5847" class="Bound">l2</a> <a id="5850" class="Symbol">:</a> <a id="5852" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5857" class="Symbol">}</a> <a id="5859" class="Symbol">(</a><a id="5860" href="metric-spaces.complete-metric-spaces.html#5860" class="Bound">A</a> <a id="5862" class="Symbol">:</a> <a id="5864" href="metric-spaces.complete-metric-spaces.html#1856" class="Function">Complete-Metric-Space</a> <a id="5886" href="metric-spaces.complete-metric-spaces.html#5844" class="Bound">l1</a> <a id="5889" href="metric-spaces.complete-metric-spaces.html#5847" class="Bound">l2</a><a id="5891" class="Symbol">)</a>
  <a id="5895" class="Symbol">(</a><a id="5896" href="metric-spaces.complete-metric-spaces.html#5896" class="Bound">f</a> <a id="5898" class="Symbol">:</a> <a id="5900" href="metric-spaces.cauchy-approximations-metric-spaces.html#1957" class="Function">cauchy-approximation-Metric-Space</a> <a id="5934" class="Symbol">(</a><a id="5935" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="5970" href="metric-spaces.complete-metric-spaces.html#5860" class="Bound">A</a><a id="5971" class="Symbol">))</a>
  <a id="5976" class="Keyword">where</a>

  <a id="5985" class="Keyword">abstract</a>
    <a id="5998" href="metric-spaces.complete-metric-spaces.html#5998" class="Function">saturated-is-limit-limit-cauchy-approximation-Complete-Metric-Space</a> <a id="6066" class="Symbol">:</a>
      <a id="6074" class="Symbol">(</a><a id="6075" href="metric-spaces.complete-metric-spaces.html#6075" class="Bound">ε</a> <a id="6077" class="Symbol">:</a> <a id="6079" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a><a id="6081" class="Symbol">)</a> <a id="6083" class="Symbol">→</a>
      <a id="6091" href="metric-spaces.complete-metric-spaces.html#2478" class="Function">neighborhood-Complete-Metric-Space</a> <a id="6126" href="metric-spaces.complete-metric-spaces.html#5860" class="Bound">A</a>
        <a id="6136" class="Symbol">(</a> <a id="6138" href="metric-spaces.complete-metric-spaces.html#6075" class="Bound">ε</a><a id="6139" class="Symbol">)</a>
        <a id="6149" class="Symbol">(</a> <a id="6151" href="metric-spaces.cauchy-approximations-metric-spaces.html#2223" class="Function">map-cauchy-approximation-Metric-Space</a>
          <a id="6199" class="Symbol">(</a> <a id="6201" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="6236" href="metric-spaces.complete-metric-spaces.html#5860" class="Bound">A</a><a id="6237" class="Symbol">)</a>
          <a id="6249" class="Symbol">(</a> <a id="6251" href="metric-spaces.complete-metric-spaces.html#5896" class="Bound">f</a><a id="6252" class="Symbol">)</a>
          <a id="6264" class="Symbol">(</a> <a id="6266" href="metric-spaces.complete-metric-spaces.html#6075" class="Bound">ε</a><a id="6267" class="Symbol">))</a>
        <a id="6278" class="Symbol">(</a> <a id="6280" href="metric-spaces.complete-metric-spaces.html#5021" class="Function">limit-cauchy-approximation-Complete-Metric-Space</a> <a id="6329" href="metric-spaces.complete-metric-spaces.html#5860" class="Bound">A</a> <a id="6331" href="metric-spaces.complete-metric-spaces.html#5896" class="Bound">f</a><a id="6332" class="Symbol">)</a>
    <a id="6338" href="metric-spaces.complete-metric-spaces.html#5998" class="Function">saturated-is-limit-limit-cauchy-approximation-Complete-Metric-Space</a> <a id="6406" class="Symbol">=</a>
      <a id="6414" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html#2452" class="Function">saturated-is-limit-cauchy-approximation-Metric-Space</a>
        <a id="6475" class="Symbol">(</a> <a id="6477" href="metric-spaces.complete-metric-spaces.html#2075" class="Function">metric-space-Complete-Metric-Space</a> <a id="6512" href="metric-spaces.complete-metric-spaces.html#5860" class="Bound">A</a><a id="6513" class="Symbol">)</a>
        <a id="6523" class="Symbol">(</a> <a id="6525" href="metric-spaces.complete-metric-spaces.html#5896" class="Bound">f</a><a id="6526" class="Symbol">)</a>
        <a id="6536" class="Symbol">(</a> <a id="6538" href="metric-spaces.complete-metric-spaces.html#5021" class="Function">limit-cauchy-approximation-Complete-Metric-Space</a> <a id="6587" href="metric-spaces.complete-metric-spaces.html#5860" class="Bound">A</a> <a id="6589" href="metric-spaces.complete-metric-spaces.html#5896" class="Bound">f</a><a id="6590" class="Symbol">)</a>
        <a id="6600" class="Symbol">(</a> <a id="6602" href="metric-spaces.complete-metric-spaces.html#5329" class="Function">is-limit-limit-cauchy-approximation-Complete-Metric-Space</a> <a id="6660" href="metric-spaces.complete-metric-spaces.html#5860" class="Bound">A</a> <a id="6662" href="metric-spaces.complete-metric-spaces.html#5896" class="Bound">f</a><a id="6663" class="Symbol">)</a>
</pre>
## External links

- [Complete metric space](https://en.wikipedia.org/wiki/Complete_metric_space)
  at Wikipedia
