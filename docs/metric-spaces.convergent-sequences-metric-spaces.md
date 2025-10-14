# Convergent sequences in metric spaces

<pre class="Agda"><a id="50" class="Keyword">module</a> <a id="57" href="metric-spaces.convergent-sequences-metric-spaces.html" class="Module">metric-spaces.convergent-sequences-metric-spaces</a> <a id="106" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="276" class="Keyword">open</a> <a id="281" class="Keyword">import</a> <a id="288" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="316" class="Keyword">open</a> <a id="321" class="Keyword">import</a> <a id="328" href="lists.sequences.html" class="Module">lists.sequences</a>

<a id="345" class="Keyword">open</a> <a id="350" class="Keyword">import</a> <a id="357" href="metric-spaces.limits-of-sequences-metric-spaces.html" class="Module">metric-spaces.limits-of-sequences-metric-spaces</a>
<a id="405" class="Keyword">open</a> <a id="410" class="Keyword">import</a> <a id="417" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
<a id="445" class="Keyword">open</a> <a id="450" class="Keyword">import</a> <a id="457" href="metric-spaces.sequences-metric-spaces.html" class="Module">metric-spaces.sequences-metric-spaces</a>
<a id="495" class="Keyword">open</a> <a id="500" class="Keyword">import</a> <a id="507" href="metric-spaces.short-functions-metric-spaces.html" class="Module">metric-spaces.short-functions-metric-spaces</a>
</pre>
</details>

## Idea

A [sequence](metric-spaces.sequences-metric-spaces.md) in a
[metric space](metric-spaces.metric-spaces.md) is
{{#concept "convergent" Disambiguation="sequence in a metric space" Agda=convergent-sequence-Metric-Space}}
if it has a [limit](metric-spaces.limits-of-sequences-metric-spaces.md).
[Short maps](metric-spaces.short-functions-metric-spaces.md) between metric
spaces preserve convergent sequences.

## Definitions

### Convergent sequences in metric spaces

<pre class="Agda"><a id="1050" class="Keyword">module</a> <a id="1057" href="metric-spaces.convergent-sequences-metric-spaces.html#1057" class="Module">_</a>
  <a id="1061" class="Symbol">{</a><a id="1062" href="metric-spaces.convergent-sequences-metric-spaces.html#1062" class="Bound">l1</a> <a id="1065" href="metric-spaces.convergent-sequences-metric-spaces.html#1065" class="Bound">l2</a> <a id="1068" class="Symbol">:</a> <a id="1070" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1075" class="Symbol">}</a> <a id="1077" class="Symbol">(</a><a id="1078" href="metric-spaces.convergent-sequences-metric-spaces.html#1078" class="Bound">M</a> <a id="1080" class="Symbol">:</a> <a id="1082" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1095" href="metric-spaces.convergent-sequences-metric-spaces.html#1062" class="Bound">l1</a> <a id="1098" href="metric-spaces.convergent-sequences-metric-spaces.html#1065" class="Bound">l2</a><a id="1100" class="Symbol">)</a>
  <a id="1104" class="Keyword">where</a>

  <a id="1113" href="metric-spaces.convergent-sequences-metric-spaces.html#1113" class="Function">subtype-convergent-sequence-Metric-Space</a> <a id="1154" class="Symbol">:</a>
    <a id="1160" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="1168" class="Symbol">(</a><a id="1169" href="metric-spaces.convergent-sequences-metric-spaces.html#1062" class="Bound">l1</a> <a id="1172" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1174" href="metric-spaces.convergent-sequences-metric-spaces.html#1065" class="Bound">l2</a><a id="1176" class="Symbol">)</a> <a id="1178" class="Symbol">(</a><a id="1179" href="metric-spaces.sequences-metric-spaces.html#804" class="Function">sequence-type-Metric-Space</a> <a id="1206" href="metric-spaces.convergent-sequences-metric-spaces.html#1078" class="Bound">M</a><a id="1207" class="Symbol">)</a>
  <a id="1211" href="metric-spaces.convergent-sequences-metric-spaces.html#1113" class="Function">subtype-convergent-sequence-Metric-Space</a> <a id="1252" class="Symbol">=</a>
    <a id="1258" href="metric-spaces.limits-of-sequences-metric-spaces.html#7238" class="Function">has-limit-prop-sequence-Metric-Space</a> <a id="1295" href="metric-spaces.convergent-sequences-metric-spaces.html#1078" class="Bound">M</a>

  <a id="1300" href="metric-spaces.convergent-sequences-metric-spaces.html#1300" class="Function">convergent-sequence-Metric-Space</a> <a id="1333" class="Symbol">:</a> <a id="1335" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1338" class="Symbol">(</a><a id="1339" href="metric-spaces.convergent-sequences-metric-spaces.html#1062" class="Bound">l1</a> <a id="1342" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1344" href="metric-spaces.convergent-sequences-metric-spaces.html#1065" class="Bound">l2</a><a id="1346" class="Symbol">)</a>
  <a id="1350" href="metric-spaces.convergent-sequences-metric-spaces.html#1300" class="Function">convergent-sequence-Metric-Space</a> <a id="1383" class="Symbol">=</a>
    <a id="1389" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="1402" href="metric-spaces.convergent-sequences-metric-spaces.html#1113" class="Function">subtype-convergent-sequence-Metric-Space</a>

<a id="1444" class="Keyword">module</a> <a id="1451" href="metric-spaces.convergent-sequences-metric-spaces.html#1451" class="Module">_</a>
  <a id="1455" class="Symbol">{</a><a id="1456" href="metric-spaces.convergent-sequences-metric-spaces.html#1456" class="Bound">l1</a> <a id="1459" href="metric-spaces.convergent-sequences-metric-spaces.html#1459" class="Bound">l2</a> <a id="1462" class="Symbol">:</a> <a id="1464" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1469" class="Symbol">}</a> <a id="1471" class="Symbol">(</a><a id="1472" href="metric-spaces.convergent-sequences-metric-spaces.html#1472" class="Bound">M</a> <a id="1474" class="Symbol">:</a> <a id="1476" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1489" href="metric-spaces.convergent-sequences-metric-spaces.html#1456" class="Bound">l1</a> <a id="1492" href="metric-spaces.convergent-sequences-metric-spaces.html#1459" class="Bound">l2</a><a id="1494" class="Symbol">)</a>
  <a id="1498" class="Symbol">(</a><a id="1499" href="metric-spaces.convergent-sequences-metric-spaces.html#1499" class="Bound">u</a> <a id="1501" class="Symbol">:</a> <a id="1503" href="metric-spaces.convergent-sequences-metric-spaces.html#1300" class="Function">convergent-sequence-Metric-Space</a> <a id="1536" href="metric-spaces.convergent-sequences-metric-spaces.html#1472" class="Bound">M</a><a id="1537" class="Symbol">)</a>
  <a id="1541" class="Keyword">where</a>

  <a id="1550" href="metric-spaces.convergent-sequences-metric-spaces.html#1550" class="Function">seq-convergent-sequence-Metric-Space</a> <a id="1587" class="Symbol">:</a> <a id="1589" href="metric-spaces.sequences-metric-spaces.html#804" class="Function">sequence-type-Metric-Space</a> <a id="1616" href="metric-spaces.convergent-sequences-metric-spaces.html#1472" class="Bound">M</a>
  <a id="1620" href="metric-spaces.convergent-sequences-metric-spaces.html#1550" class="Function">seq-convergent-sequence-Metric-Space</a> <a id="1657" class="Symbol">=</a> <a id="1659" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1663" href="metric-spaces.convergent-sequences-metric-spaces.html#1499" class="Bound">u</a>

  <a id="1668" href="metric-spaces.convergent-sequences-metric-spaces.html#1668" class="Function">has-limit-convergent-sequence-Metric-Space</a> <a id="1711" class="Symbol">:</a>
    <a id="1717" href="metric-spaces.limits-of-sequences-metric-spaces.html#6150" class="Function">has-limit-sequence-Metric-Space</a> <a id="1749" href="metric-spaces.convergent-sequences-metric-spaces.html#1472" class="Bound">M</a> <a id="1751" href="metric-spaces.convergent-sequences-metric-spaces.html#1550" class="Function">seq-convergent-sequence-Metric-Space</a>
  <a id="1790" href="metric-spaces.convergent-sequences-metric-spaces.html#1668" class="Function">has-limit-convergent-sequence-Metric-Space</a> <a id="1833" class="Symbol">=</a> <a id="1835" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1839" href="metric-spaces.convergent-sequences-metric-spaces.html#1499" class="Bound">u</a>

  <a id="1844" href="metric-spaces.convergent-sequences-metric-spaces.html#1844" class="Function">limit-convergent-sequence-Metric-Space</a> <a id="1883" class="Symbol">:</a> <a id="1885" href="metric-spaces.metric-spaces.html#5090" class="Function">type-Metric-Space</a> <a id="1903" href="metric-spaces.convergent-sequences-metric-spaces.html#1472" class="Bound">M</a>
  <a id="1907" href="metric-spaces.convergent-sequences-metric-spaces.html#1844" class="Function">limit-convergent-sequence-Metric-Space</a> <a id="1946" class="Symbol">=</a>
    <a id="1952" href="metric-spaces.limits-of-sequences-metric-spaces.html#6301" class="Function">limit-has-limit-sequence-Metric-Space</a> <a id="1990" href="metric-spaces.convergent-sequences-metric-spaces.html#1472" class="Bound">M</a>
      <a id="1998" href="metric-spaces.convergent-sequences-metric-spaces.html#1550" class="Function">seq-convergent-sequence-Metric-Space</a>
      <a id="2041" href="metric-spaces.convergent-sequences-metric-spaces.html#1668" class="Function">has-limit-convergent-sequence-Metric-Space</a>

  <a id="2087" href="metric-spaces.convergent-sequences-metric-spaces.html#2087" class="Function">is-limit-limit-convergent-sequence-Metric-Space</a> <a id="2135" class="Symbol">:</a>
    <a id="2141" href="metric-spaces.limits-of-sequences-metric-spaces.html#2959" class="Function">is-limit-sequence-Metric-Space</a> <a id="2172" href="metric-spaces.convergent-sequences-metric-spaces.html#1472" class="Bound">M</a>
      <a id="2180" href="metric-spaces.convergent-sequences-metric-spaces.html#1550" class="Function">seq-convergent-sequence-Metric-Space</a>
      <a id="2223" href="metric-spaces.convergent-sequences-metric-spaces.html#1844" class="Function">limit-convergent-sequence-Metric-Space</a>
  <a id="2264" href="metric-spaces.convergent-sequences-metric-spaces.html#2087" class="Function">is-limit-limit-convergent-sequence-Metric-Space</a> <a id="2312" class="Symbol">=</a>
    <a id="2318" href="metric-spaces.limits-of-sequences-metric-spaces.html#6452" class="Function">is-limit-limit-has-limit-sequence-Metric-Space</a> <a id="2365" href="metric-spaces.convergent-sequences-metric-spaces.html#1472" class="Bound">M</a>
      <a id="2373" href="metric-spaces.convergent-sequences-metric-spaces.html#1550" class="Function">seq-convergent-sequence-Metric-Space</a>
      <a id="2416" href="metric-spaces.convergent-sequences-metric-spaces.html#1668" class="Function">has-limit-convergent-sequence-Metric-Space</a>
</pre>
## Properties

### Short maps between metric spaces preserve convergent sequences and their limits

<pre class="Agda"><a id="2572" class="Keyword">module</a> <a id="2579" href="metric-spaces.convergent-sequences-metric-spaces.html#2579" class="Module">_</a>
  <a id="2583" class="Symbol">{</a><a id="2584" href="metric-spaces.convergent-sequences-metric-spaces.html#2584" class="Bound">l1</a> <a id="2587" href="metric-spaces.convergent-sequences-metric-spaces.html#2587" class="Bound">l2</a> <a id="2590" href="metric-spaces.convergent-sequences-metric-spaces.html#2590" class="Bound">l1&#39;</a> <a id="2594" href="metric-spaces.convergent-sequences-metric-spaces.html#2594" class="Bound">l2&#39;</a> <a id="2598" class="Symbol">:</a> <a id="2600" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2605" class="Symbol">}</a>
  <a id="2609" class="Symbol">(</a><a id="2610" href="metric-spaces.convergent-sequences-metric-spaces.html#2610" class="Bound">A</a> <a id="2612" class="Symbol">:</a> <a id="2614" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="2627" href="metric-spaces.convergent-sequences-metric-spaces.html#2584" class="Bound">l1</a> <a id="2630" href="metric-spaces.convergent-sequences-metric-spaces.html#2587" class="Bound">l2</a><a id="2632" class="Symbol">)</a> <a id="2634" class="Symbol">(</a><a id="2635" href="metric-spaces.convergent-sequences-metric-spaces.html#2635" class="Bound">B</a> <a id="2637" class="Symbol">:</a> <a id="2639" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="2652" href="metric-spaces.convergent-sequences-metric-spaces.html#2590" class="Bound">l1&#39;</a> <a id="2656" href="metric-spaces.convergent-sequences-metric-spaces.html#2594" class="Bound">l2&#39;</a><a id="2659" class="Symbol">)</a>
  <a id="2663" class="Symbol">(</a><a id="2664" href="metric-spaces.convergent-sequences-metric-spaces.html#2664" class="Bound">f</a> <a id="2666" class="Symbol">:</a> <a id="2668" href="metric-spaces.short-functions-metric-spaces.html#2932" class="Function">short-function-Metric-Space</a> <a id="2696" href="metric-spaces.convergent-sequences-metric-spaces.html#2610" class="Bound">A</a> <a id="2698" href="metric-spaces.convergent-sequences-metric-spaces.html#2635" class="Bound">B</a><a id="2699" class="Symbol">)</a>
  <a id="2703" class="Symbol">(</a><a id="2704" href="metric-spaces.convergent-sequences-metric-spaces.html#2704" class="Bound">u</a> <a id="2706" class="Symbol">:</a> <a id="2708" href="metric-spaces.convergent-sequences-metric-spaces.html#1300" class="Function">convergent-sequence-Metric-Space</a> <a id="2741" href="metric-spaces.convergent-sequences-metric-spaces.html#2610" class="Bound">A</a><a id="2742" class="Symbol">)</a>
  <a id="2746" class="Keyword">where</a>

  <a id="2755" href="metric-spaces.convergent-sequences-metric-spaces.html#2755" class="Function">seq-short-map-convergent-sequence-Metric-Space</a> <a id="2802" class="Symbol">:</a> <a id="2804" href="metric-spaces.sequences-metric-spaces.html#804" class="Function">sequence-type-Metric-Space</a> <a id="2831" href="metric-spaces.convergent-sequences-metric-spaces.html#2635" class="Bound">B</a>
  <a id="2835" href="metric-spaces.convergent-sequences-metric-spaces.html#2755" class="Function">seq-short-map-convergent-sequence-Metric-Space</a> <a id="2882" class="Symbol">=</a>
    <a id="2888" href="lists.sequences.html#818" class="Function">map-sequence</a>
      <a id="2907" class="Symbol">(</a> <a id="2909" href="metric-spaces.short-functions-metric-spaces.html#3644" class="Function">map-short-function-Metric-Space</a> <a id="2941" href="metric-spaces.convergent-sequences-metric-spaces.html#2610" class="Bound">A</a> <a id="2943" href="metric-spaces.convergent-sequences-metric-spaces.html#2635" class="Bound">B</a> <a id="2945" href="metric-spaces.convergent-sequences-metric-spaces.html#2664" class="Bound">f</a><a id="2946" class="Symbol">)</a>
      <a id="2954" class="Symbol">(</a> <a id="2956" href="metric-spaces.convergent-sequences-metric-spaces.html#1550" class="Function">seq-convergent-sequence-Metric-Space</a> <a id="2993" href="metric-spaces.convergent-sequences-metric-spaces.html#2610" class="Bound">A</a> <a id="2995" href="metric-spaces.convergent-sequences-metric-spaces.html#2704" class="Bound">u</a><a id="2996" class="Symbol">)</a>

  <a id="3001" href="metric-spaces.convergent-sequences-metric-spaces.html#3001" class="Function">has-limit-seq-short-map-convergent-sequence-Metric-Space</a> <a id="3058" class="Symbol">:</a>
    <a id="3064" href="metric-spaces.limits-of-sequences-metric-spaces.html#6150" class="Function">has-limit-sequence-Metric-Space</a> <a id="3096" href="metric-spaces.convergent-sequences-metric-spaces.html#2635" class="Bound">B</a>
      <a id="3104" href="metric-spaces.convergent-sequences-metric-spaces.html#2755" class="Function">seq-short-map-convergent-sequence-Metric-Space</a>
  <a id="3153" href="metric-spaces.convergent-sequences-metric-spaces.html#3001" class="Function">has-limit-seq-short-map-convergent-sequence-Metric-Space</a> <a id="3210" class="Symbol">=</a>
    <a id="3216" class="Symbol">(</a> <a id="3218" href="metric-spaces.short-functions-metric-spaces.html#3644" class="Function">map-short-function-Metric-Space</a> <a id="3250" href="metric-spaces.convergent-sequences-metric-spaces.html#2610" class="Bound">A</a> <a id="3252" href="metric-spaces.convergent-sequences-metric-spaces.html#2635" class="Bound">B</a> <a id="3254" href="metric-spaces.convergent-sequences-metric-spaces.html#2664" class="Bound">f</a>
      <a id="3262" class="Symbol">(</a> <a id="3264" href="metric-spaces.convergent-sequences-metric-spaces.html#1844" class="Function">limit-convergent-sequence-Metric-Space</a> <a id="3303" href="metric-spaces.convergent-sequences-metric-spaces.html#2610" class="Bound">A</a> <a id="3305" href="metric-spaces.convergent-sequences-metric-spaces.html#2704" class="Bound">u</a><a id="3306" class="Symbol">))</a> <a id="3309" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="3315" class="Symbol">(</a> <a id="3317" href="metric-spaces.limits-of-sequences-metric-spaces.html#8140" class="Function">short-map-limit-sequence-Metric-Space</a>
      <a id="3361" class="Symbol">(</a> <a id="3363" href="metric-spaces.convergent-sequences-metric-spaces.html#2610" class="Bound">A</a><a id="3364" class="Symbol">)</a>
      <a id="3372" class="Symbol">(</a> <a id="3374" href="metric-spaces.convergent-sequences-metric-spaces.html#2635" class="Bound">B</a><a id="3375" class="Symbol">)</a>
      <a id="3383" class="Symbol">(</a> <a id="3385" href="metric-spaces.convergent-sequences-metric-spaces.html#2664" class="Bound">f</a><a id="3386" class="Symbol">)</a>
      <a id="3394" class="Symbol">(</a> <a id="3396" href="metric-spaces.convergent-sequences-metric-spaces.html#1550" class="Function">seq-convergent-sequence-Metric-Space</a> <a id="3433" href="metric-spaces.convergent-sequences-metric-spaces.html#2610" class="Bound">A</a> <a id="3435" href="metric-spaces.convergent-sequences-metric-spaces.html#2704" class="Bound">u</a><a id="3436" class="Symbol">)</a>
      <a id="3444" class="Symbol">(</a> <a id="3446" href="metric-spaces.convergent-sequences-metric-spaces.html#1844" class="Function">limit-convergent-sequence-Metric-Space</a> <a id="3485" href="metric-spaces.convergent-sequences-metric-spaces.html#2610" class="Bound">A</a> <a id="3487" href="metric-spaces.convergent-sequences-metric-spaces.html#2704" class="Bound">u</a><a id="3488" class="Symbol">)</a>
      <a id="3496" class="Symbol">(</a> <a id="3498" href="metric-spaces.convergent-sequences-metric-spaces.html#2087" class="Function">is-limit-limit-convergent-sequence-Metric-Space</a> <a id="3546" href="metric-spaces.convergent-sequences-metric-spaces.html#2610" class="Bound">A</a> <a id="3548" href="metric-spaces.convergent-sequences-metric-spaces.html#2704" class="Bound">u</a><a id="3549" class="Symbol">))</a>

  <a id="3555" href="metric-spaces.convergent-sequences-metric-spaces.html#3555" class="Function">map-short-map-convergent-sequence-Metric-Space</a> <a id="3602" class="Symbol">:</a>
    <a id="3608" href="metric-spaces.convergent-sequences-metric-spaces.html#1300" class="Function">convergent-sequence-Metric-Space</a> <a id="3641" href="metric-spaces.convergent-sequences-metric-spaces.html#2635" class="Bound">B</a>
  <a id="3645" href="metric-spaces.convergent-sequences-metric-spaces.html#3555" class="Function">map-short-map-convergent-sequence-Metric-Space</a> <a id="3692" class="Symbol">=</a>
    <a id="3698" href="metric-spaces.convergent-sequences-metric-spaces.html#2755" class="Function">seq-short-map-convergent-sequence-Metric-Space</a> <a id="3745" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="3751" href="metric-spaces.convergent-sequences-metric-spaces.html#3001" class="Function">has-limit-seq-short-map-convergent-sequence-Metric-Space</a>

  <a id="3811" href="metric-spaces.convergent-sequences-metric-spaces.html#3811" class="Function">eq-limit-short-map-convergent-sequence-Metric-Space</a> <a id="3863" class="Symbol">:</a>
    <a id="3869" class="Symbol">(</a> <a id="3871" href="metric-spaces.short-functions-metric-spaces.html#3644" class="Function">map-short-function-Metric-Space</a> <a id="3903" href="metric-spaces.convergent-sequences-metric-spaces.html#2610" class="Bound">A</a> <a id="3905" href="metric-spaces.convergent-sequences-metric-spaces.html#2635" class="Bound">B</a> <a id="3907" href="metric-spaces.convergent-sequences-metric-spaces.html#2664" class="Bound">f</a>
      <a id="3915" class="Symbol">(</a> <a id="3917" href="metric-spaces.convergent-sequences-metric-spaces.html#1844" class="Function">limit-convergent-sequence-Metric-Space</a> <a id="3956" href="metric-spaces.convergent-sequences-metric-spaces.html#2610" class="Bound">A</a> <a id="3958" href="metric-spaces.convergent-sequences-metric-spaces.html#2704" class="Bound">u</a><a id="3959" class="Symbol">))</a> <a id="3962" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="3968" class="Symbol">(</a> <a id="3970" href="metric-spaces.convergent-sequences-metric-spaces.html#1844" class="Function">limit-convergent-sequence-Metric-Space</a> <a id="4009" href="metric-spaces.convergent-sequences-metric-spaces.html#2635" class="Bound">B</a>
      <a id="4017" class="Symbol">(</a> <a id="4019" href="metric-spaces.convergent-sequences-metric-spaces.html#3555" class="Function">map-short-map-convergent-sequence-Metric-Space</a><a id="4065" class="Symbol">))</a>
  <a id="4070" href="metric-spaces.convergent-sequences-metric-spaces.html#3811" class="Function">eq-limit-short-map-convergent-sequence-Metric-Space</a> <a id="4122" class="Symbol">=</a> <a id="4124" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
## See also

- The
  [metric space of convergent sequences](metric-spaces.metric-space-of-convergent-sequences-metric-spaces.md)
  in a metric space
