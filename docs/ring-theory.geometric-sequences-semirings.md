# Geometric sequences in semirings

<pre class="Agda"><a id="45" class="Keyword">module</a> <a id="52" href="ring-theory.geometric-sequences-semirings.html" class="Module">ring-theory.geometric-sequences-semirings</a> <a id="94" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="150" class="Keyword">open</a> <a id="155" class="Keyword">import</a> <a id="162" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="204" class="Keyword">open</a> <a id="209" class="Keyword">import</a> <a id="216" href="foundation.action-on-identifications-binary-functions.html" class="Module">foundation.action-on-identifications-binary-functions</a>
<a id="270" class="Keyword">open</a> <a id="275" class="Keyword">import</a> <a id="282" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="329" class="Keyword">open</a> <a id="334" class="Keyword">import</a> <a id="341" href="foundation.binary-transport.html" class="Module">foundation.binary-transport</a>
<a id="369" class="Keyword">open</a> <a id="374" class="Keyword">import</a> <a id="381" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="413" class="Keyword">open</a> <a id="418" class="Keyword">import</a> <a id="425" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="447" class="Keyword">open</a> <a id="452" class="Keyword">import</a> <a id="459" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="485" class="Keyword">open</a> <a id="490" class="Keyword">import</a> <a id="497" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="521" class="Keyword">open</a> <a id="526" class="Keyword">import</a> <a id="533" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="549" class="Keyword">open</a> <a id="554" class="Keyword">import</a> <a id="561" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="589" class="Keyword">open</a> <a id="594" class="Keyword">import</a> <a id="601" href="group-theory.arithmetic-sequences-semigroups.html" class="Module">group-theory.arithmetic-sequences-semigroups</a>

<a id="647" class="Keyword">open</a> <a id="652" class="Keyword">import</a> <a id="659" href="lists.sequences.html" class="Module">lists.sequences</a>

<a id="676" class="Keyword">open</a> <a id="681" class="Keyword">import</a> <a id="688" href="ring-theory.powers-of-elements-semirings.html" class="Module">ring-theory.powers-of-elements-semirings</a>
<a id="729" class="Keyword">open</a> <a id="734" class="Keyword">import</a> <a id="741" href="ring-theory.semirings.html" class="Module">ring-theory.semirings</a>
</pre>
</details>

## Ideas

A
{{#concept "geometric sequence" Disambiguation="in a semiring" Agda=geometric-sequence-Semiring}}
in a [semiring](ring-theory.semirings.md) is an
[arithmetic sequence](group-theory.arithmetic-sequences-semigroups.md) in the
semiring multiplicative [semigroup](group-theory.semigroups.md).

These are sequences of the form `n ↦ a * rⁿ`, for elements `a`, `r` in the
semiring.

## Definitions

### Geometric sequences in semirings

<pre class="Agda"><a id="1230" class="Keyword">module</a> <a id="1237" href="ring-theory.geometric-sequences-semirings.html#1237" class="Module">_</a>
  <a id="1241" class="Symbol">{</a><a id="1242" href="ring-theory.geometric-sequences-semirings.html#1242" class="Bound">l</a> <a id="1244" class="Symbol">:</a> <a id="1246" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1251" class="Symbol">}</a> <a id="1253" class="Symbol">(</a><a id="1254" href="ring-theory.geometric-sequences-semirings.html#1254" class="Bound">R</a> <a id="1256" class="Symbol">:</a> <a id="1258" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="1267" href="ring-theory.geometric-sequences-semirings.html#1242" class="Bound">l</a><a id="1268" class="Symbol">)</a>
  <a id="1272" class="Keyword">where</a>

  <a id="1281" href="ring-theory.geometric-sequences-semirings.html#1281" class="Function">geometric-sequence-Semiring</a> <a id="1309" class="Symbol">:</a> <a id="1311" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1314" href="ring-theory.geometric-sequences-semirings.html#1242" class="Bound">l</a>
  <a id="1318" href="ring-theory.geometric-sequences-semirings.html#1281" class="Function">geometric-sequence-Semiring</a> <a id="1346" class="Symbol">=</a>
    <a id="1352" href="group-theory.arithmetic-sequences-semigroups.html#2216" class="Function">arithmetic-sequence-Semigroup</a>
      <a id="1388" class="Symbol">(</a> <a id="1390" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="1424" href="ring-theory.geometric-sequences-semirings.html#1254" class="Bound">R</a><a id="1425" class="Symbol">)</a>

<a id="1428" class="Keyword">module</a> <a id="1435" href="ring-theory.geometric-sequences-semirings.html#1435" class="Module">_</a>
  <a id="1439" class="Symbol">{</a><a id="1440" href="ring-theory.geometric-sequences-semirings.html#1440" class="Bound">l</a> <a id="1442" class="Symbol">:</a> <a id="1444" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1449" class="Symbol">}</a> <a id="1451" class="Symbol">(</a><a id="1452" href="ring-theory.geometric-sequences-semirings.html#1452" class="Bound">R</a> <a id="1454" class="Symbol">:</a> <a id="1456" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="1465" href="ring-theory.geometric-sequences-semirings.html#1440" class="Bound">l</a><a id="1466" class="Symbol">)</a>
  <a id="1470" class="Symbol">(</a><a id="1471" href="ring-theory.geometric-sequences-semirings.html#1471" class="Bound">u</a> <a id="1473" class="Symbol">:</a> <a id="1475" href="ring-theory.geometric-sequences-semirings.html#1281" class="Function">geometric-sequence-Semiring</a> <a id="1503" href="ring-theory.geometric-sequences-semirings.html#1452" class="Bound">R</a><a id="1504" class="Symbol">)</a>
  <a id="1508" class="Keyword">where</a>

  <a id="1517" href="ring-theory.geometric-sequences-semirings.html#1517" class="Function">seq-geometric-sequence-Semiring</a> <a id="1549" class="Symbol">:</a> <a id="1551" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1553" class="Symbol">→</a> <a id="1555" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="1569" href="ring-theory.geometric-sequences-semirings.html#1452" class="Bound">R</a>
  <a id="1573" href="ring-theory.geometric-sequences-semirings.html#1517" class="Function">seq-geometric-sequence-Semiring</a> <a id="1605" class="Symbol">=</a>
    <a id="1611" href="group-theory.arithmetic-sequences-semigroups.html#2444" class="Function">seq-arithmetic-sequence-Semigroup</a>
      <a id="1651" class="Symbol">(</a> <a id="1653" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="1687" href="ring-theory.geometric-sequences-semirings.html#1452" class="Bound">R</a><a id="1688" class="Symbol">)</a>
      <a id="1696" class="Symbol">(</a> <a id="1698" href="ring-theory.geometric-sequences-semirings.html#1471" class="Bound">u</a><a id="1699" class="Symbol">)</a>

  <a id="1704" href="ring-theory.geometric-sequences-semirings.html#1704" class="Function">is-geometric-seq-geometric-sequence-Semiring</a> <a id="1749" class="Symbol">:</a>
    <a id="1755" href="group-theory.arithmetic-sequences-semigroups.html#1966" class="Function">is-arithmetic-sequence-Semigroup</a>
      <a id="1794" class="Symbol">(</a> <a id="1796" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="1830" href="ring-theory.geometric-sequences-semirings.html#1452" class="Bound">R</a><a id="1831" class="Symbol">)</a>
      <a id="1839" class="Symbol">(</a> <a id="1841" href="ring-theory.geometric-sequences-semirings.html#1517" class="Function">seq-geometric-sequence-Semiring</a><a id="1872" class="Symbol">)</a>
  <a id="1876" href="ring-theory.geometric-sequences-semirings.html#1704" class="Function">is-geometric-seq-geometric-sequence-Semiring</a> <a id="1921" class="Symbol">=</a>
    <a id="1927" href="group-theory.arithmetic-sequences-semigroups.html#2548" class="Function">is-arithmetic-seq-arithmetic-sequence-Semigroup</a>
      <a id="1981" class="Symbol">(</a> <a id="1983" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="2017" href="ring-theory.geometric-sequences-semirings.html#1452" class="Bound">R</a><a id="2018" class="Symbol">)</a>
      <a id="2026" class="Symbol">(</a> <a id="2028" href="ring-theory.geometric-sequences-semirings.html#1471" class="Bound">u</a><a id="2029" class="Symbol">)</a>

  <a id="2034" href="ring-theory.geometric-sequences-semirings.html#2034" class="Function">common-ratio-geometric-sequence-Semiring</a> <a id="2075" class="Symbol">:</a> <a id="2077" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="2091" href="ring-theory.geometric-sequences-semirings.html#1452" class="Bound">R</a>
  <a id="2095" href="ring-theory.geometric-sequences-semirings.html#2034" class="Function">common-ratio-geometric-sequence-Semiring</a> <a id="2136" class="Symbol">=</a>
    <a id="2142" href="group-theory.arithmetic-sequences-semigroups.html#2732" class="Function">common-difference-arithmetic-sequence-Semigroup</a>
      <a id="2196" class="Symbol">(</a> <a id="2198" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="2232" href="ring-theory.geometric-sequences-semirings.html#1452" class="Bound">R</a><a id="2233" class="Symbol">)</a>
      <a id="2241" class="Symbol">(</a> <a id="2243" href="ring-theory.geometric-sequences-semirings.html#1471" class="Bound">u</a><a id="2244" class="Symbol">)</a>

  <a id="2249" href="ring-theory.geometric-sequences-semirings.html#2249" class="Function">is-common-ratio-geometric-sequence-Semiring</a> <a id="2293" class="Symbol">:</a>
    <a id="2299" class="Symbol">(</a> <a id="2301" href="ring-theory.geometric-sequences-semirings.html#2301" class="Bound">n</a> <a id="2303" class="Symbol">:</a> <a id="2305" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2306" class="Symbol">)</a> <a id="2308" class="Symbol">→</a>
    <a id="2314" class="Symbol">(</a> <a id="2316" href="ring-theory.geometric-sequences-semirings.html#1517" class="Function">seq-geometric-sequence-Semiring</a> <a id="2348" class="Symbol">(</a><a id="2349" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2356" href="ring-theory.geometric-sequences-semirings.html#2301" class="Bound">n</a><a id="2357" class="Symbol">))</a> <a id="2360" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="2366" class="Symbol">(</a> <a id="2368" href="ring-theory.semirings.html#6747" class="Function">mul-Semiring</a>
      <a id="2387" class="Symbol">(</a> <a id="2389" href="ring-theory.geometric-sequences-semirings.html#1452" class="Bound">R</a><a id="2390" class="Symbol">)</a>
      <a id="2398" class="Symbol">(</a> <a id="2400" href="ring-theory.geometric-sequences-semirings.html#1517" class="Function">seq-geometric-sequence-Semiring</a> <a id="2432" href="ring-theory.geometric-sequences-semirings.html#2301" class="Bound">n</a><a id="2433" class="Symbol">)</a>
      <a id="2441" class="Symbol">(</a> <a id="2443" href="ring-theory.geometric-sequences-semirings.html#2034" class="Function">common-ratio-geometric-sequence-Semiring</a><a id="2483" class="Symbol">))</a>
  <a id="2488" href="ring-theory.geometric-sequences-semirings.html#2249" class="Function">is-common-ratio-geometric-sequence-Semiring</a> <a id="2532" class="Symbol">=</a>
    <a id="2538" href="group-theory.arithmetic-sequences-semigroups.html#2910" class="Function">is-common-difference-arithmetic-sequence-Semigroup</a>
      <a id="2595" class="Symbol">(</a> <a id="2597" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="2631" href="ring-theory.geometric-sequences-semirings.html#1452" class="Bound">R</a><a id="2632" class="Symbol">)</a>
      <a id="2640" class="Symbol">(</a> <a id="2642" href="ring-theory.geometric-sequences-semirings.html#1471" class="Bound">u</a><a id="2643" class="Symbol">)</a>

  <a id="2648" href="ring-theory.geometric-sequences-semirings.html#2648" class="Function">initial-term-geometric-sequence-Semiring</a> <a id="2689" class="Symbol">:</a> <a id="2691" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="2705" href="ring-theory.geometric-sequences-semirings.html#1452" class="Bound">R</a>
  <a id="2709" href="ring-theory.geometric-sequences-semirings.html#2648" class="Function">initial-term-geometric-sequence-Semiring</a> <a id="2750" class="Symbol">=</a>
    <a id="2756" href="group-theory.arithmetic-sequences-semigroups.html#3217" class="Function">initial-term-arithmetic-sequence-Semigroup</a>
      <a id="2805" class="Symbol">(</a> <a id="2807" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="2841" href="ring-theory.geometric-sequences-semirings.html#1452" class="Bound">R</a><a id="2842" class="Symbol">)</a>
      <a id="2850" class="Symbol">(</a> <a id="2852" href="ring-theory.geometric-sequences-semirings.html#1471" class="Bound">u</a><a id="2853" class="Symbol">)</a>
</pre>
### The standard geometric sequences in a semiring

The standard geometric sequence with initial term `a` and common factor `r` is
the sequence `u` defined by:

- `u₀ = a`
- `uₙ₊₁ = uₙ * r`

<pre class="Agda"><a id="3059" class="Keyword">module</a> <a id="3066" href="ring-theory.geometric-sequences-semirings.html#3066" class="Module">_</a>
  <a id="3070" class="Symbol">{</a><a id="3071" href="ring-theory.geometric-sequences-semirings.html#3071" class="Bound">l</a> <a id="3073" class="Symbol">:</a> <a id="3075" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3080" class="Symbol">}</a> <a id="3082" class="Symbol">(</a><a id="3083" href="ring-theory.geometric-sequences-semirings.html#3083" class="Bound">R</a> <a id="3085" class="Symbol">:</a> <a id="3087" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="3096" href="ring-theory.geometric-sequences-semirings.html#3071" class="Bound">l</a><a id="3097" class="Symbol">)</a> <a id="3099" class="Symbol">(</a><a id="3100" href="ring-theory.geometric-sequences-semirings.html#3100" class="Bound">a</a> <a id="3102" href="ring-theory.geometric-sequences-semirings.html#3102" class="Bound">r</a> <a id="3104" class="Symbol">:</a> <a id="3106" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="3120" href="ring-theory.geometric-sequences-semirings.html#3083" class="Bound">R</a><a id="3121" class="Symbol">)</a>
  <a id="3125" class="Keyword">where</a>

  <a id="3134" href="ring-theory.geometric-sequences-semirings.html#3134" class="Function">standard-geometric-sequence-Semiring</a> <a id="3171" class="Symbol">:</a> <a id="3173" href="ring-theory.geometric-sequences-semirings.html#1281" class="Function">geometric-sequence-Semiring</a> <a id="3201" href="ring-theory.geometric-sequences-semirings.html#3083" class="Bound">R</a>
  <a id="3205" href="ring-theory.geometric-sequences-semirings.html#3134" class="Function">standard-geometric-sequence-Semiring</a> <a id="3242" class="Symbol">=</a>
    <a id="3248" href="group-theory.arithmetic-sequences-semigroups.html#4169" class="Function">standard-arithmetic-sequence-Semigroup</a>
      <a id="3293" class="Symbol">(</a> <a id="3295" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="3329" href="ring-theory.geometric-sequences-semirings.html#3083" class="Bound">R</a><a id="3330" class="Symbol">)</a>
      <a id="3338" class="Symbol">(</a> <a id="3340" href="ring-theory.geometric-sequences-semirings.html#3100" class="Bound">a</a><a id="3341" class="Symbol">)</a>
      <a id="3349" class="Symbol">(</a> <a id="3351" href="ring-theory.geometric-sequences-semirings.html#3102" class="Bound">r</a><a id="3352" class="Symbol">)</a>

  <a id="3357" href="ring-theory.geometric-sequences-semirings.html#3357" class="Function">seq-standard-geometric-sequence-Semiring</a> <a id="3398" class="Symbol">:</a> <a id="3400" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="3402" class="Symbol">→</a> <a id="3404" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="3418" href="ring-theory.geometric-sequences-semirings.html#3083" class="Bound">R</a>
  <a id="3422" href="ring-theory.geometric-sequences-semirings.html#3357" class="Function">seq-standard-geometric-sequence-Semiring</a> <a id="3463" class="Symbol">=</a>
    <a id="3469" href="ring-theory.geometric-sequences-semirings.html#1517" class="Function">seq-geometric-sequence-Semiring</a> <a id="3501" href="ring-theory.geometric-sequences-semirings.html#3083" class="Bound">R</a>
      <a id="3509" href="ring-theory.geometric-sequences-semirings.html#3134" class="Function">standard-geometric-sequence-Semiring</a>

  <a id="3549" href="ring-theory.geometric-sequences-semirings.html#3549" class="Function">is-geometric-standard-geometric-sequence-Semiring</a> <a id="3599" class="Symbol">:</a>
    <a id="3605" href="group-theory.arithmetic-sequences-semigroups.html#1966" class="Function">is-arithmetic-sequence-Semigroup</a>
      <a id="3644" class="Symbol">(</a> <a id="3646" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="3680" href="ring-theory.geometric-sequences-semirings.html#3083" class="Bound">R</a><a id="3681" class="Symbol">)</a>
      <a id="3689" class="Symbol">(</a> <a id="3691" href="ring-theory.geometric-sequences-semirings.html#3357" class="Function">seq-standard-geometric-sequence-Semiring</a><a id="3731" class="Symbol">)</a>
  <a id="3735" href="ring-theory.geometric-sequences-semirings.html#3549" class="Function">is-geometric-standard-geometric-sequence-Semiring</a> <a id="3785" class="Symbol">=</a>
    <a id="3791" href="ring-theory.geometric-sequences-semirings.html#1704" class="Function">is-geometric-seq-geometric-sequence-Semiring</a> <a id="3836" href="ring-theory.geometric-sequences-semirings.html#3083" class="Bound">R</a>
      <a id="3844" href="ring-theory.geometric-sequences-semirings.html#3134" class="Function">standard-geometric-sequence-Semiring</a>
</pre>
### The geometric sequences `n ↦ a * rⁿ`

<pre class="Agda"><a id="3936" class="Keyword">module</a> <a id="3943" href="ring-theory.geometric-sequences-semirings.html#3943" class="Module">_</a>
  <a id="3947" class="Symbol">{</a><a id="3948" href="ring-theory.geometric-sequences-semirings.html#3948" class="Bound">l</a> <a id="3950" class="Symbol">:</a> <a id="3952" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3957" class="Symbol">}</a> <a id="3959" class="Symbol">(</a><a id="3960" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a> <a id="3962" class="Symbol">:</a> <a id="3964" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="3973" href="ring-theory.geometric-sequences-semirings.html#3948" class="Bound">l</a><a id="3974" class="Symbol">)</a> <a id="3976" class="Symbol">(</a><a id="3977" href="ring-theory.geometric-sequences-semirings.html#3977" class="Bound">a</a> <a id="3979" href="ring-theory.geometric-sequences-semirings.html#3979" class="Bound">r</a> <a id="3981" class="Symbol">:</a> <a id="3983" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="3997" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a><a id="3998" class="Symbol">)</a>
  <a id="4002" class="Keyword">where</a>

  <a id="4011" href="ring-theory.geometric-sequences-semirings.html#4011" class="Function">mul-pow-nat-Semiring</a> <a id="4032" class="Symbol">:</a> <a id="4034" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="4036" class="Symbol">→</a> <a id="4038" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="4052" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a>
  <a id="4056" href="ring-theory.geometric-sequences-semirings.html#4011" class="Function">mul-pow-nat-Semiring</a> <a id="4077" href="ring-theory.geometric-sequences-semirings.html#4077" class="Bound">n</a> <a id="4079" class="Symbol">=</a>
    <a id="4085" href="ring-theory.semirings.html#6747" class="Function">mul-Semiring</a> <a id="4098" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a> <a id="4100" href="ring-theory.geometric-sequences-semirings.html#3977" class="Bound">a</a> <a id="4102" class="Symbol">(</a><a id="4103" href="ring-theory.powers-of-elements-semirings.html#675" class="Function">power-Semiring</a> <a id="4118" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a> <a id="4120" href="ring-theory.geometric-sequences-semirings.html#4077" class="Bound">n</a> <a id="4122" href="ring-theory.geometric-sequences-semirings.html#3979" class="Bound">r</a><a id="4123" class="Symbol">)</a>

  <a id="4128" href="ring-theory.geometric-sequences-semirings.html#4128" class="Function">is-common-ratio-mul-pow-nat-Semiring</a> <a id="4165" class="Symbol">:</a>
    <a id="4171" href="group-theory.arithmetic-sequences-semigroups.html#1788" class="Function">is-common-difference-sequence-Semigroup</a>
      <a id="4217" class="Symbol">(</a> <a id="4219" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="4253" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a><a id="4254" class="Symbol">)</a>
      <a id="4262" class="Symbol">(</a> <a id="4264" href="ring-theory.geometric-sequences-semirings.html#4011" class="Function">mul-pow-nat-Semiring</a><a id="4284" class="Symbol">)</a>
      <a id="4292" class="Symbol">(</a> <a id="4294" href="ring-theory.geometric-sequences-semirings.html#3979" class="Bound">r</a><a id="4295" class="Symbol">)</a>
  <a id="4299" href="ring-theory.geometric-sequences-semirings.html#4128" class="Function">is-common-ratio-mul-pow-nat-Semiring</a> <a id="4336" href="ring-theory.geometric-sequences-semirings.html#4336" class="Bound">n</a> <a id="4338" class="Symbol">=</a>
    <a id="4344" class="Symbol">(</a> <a id="4346" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
      <a id="4355" class="Symbol">(</a> <a id="4357" href="ring-theory.semirings.html#6747" class="Function">mul-Semiring</a> <a id="4370" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a> <a id="4372" href="ring-theory.geometric-sequences-semirings.html#3977" class="Bound">a</a><a id="4373" class="Symbol">)</a>
      <a id="4381" class="Symbol">(</a> <a id="4383" href="ring-theory.powers-of-elements-semirings.html#1177" class="Function">power-succ-Semiring</a> <a id="4403" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a> <a id="4405" href="ring-theory.geometric-sequences-semirings.html#4336" class="Bound">n</a> <a id="4407" href="ring-theory.geometric-sequences-semirings.html#3979" class="Bound">r</a><a id="4408" class="Symbol">))</a> <a id="4411" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
    <a id="4417" class="Symbol">(</a> <a id="4419" href="foundation-core.identity-types.html#6358" class="Function">inv</a>
      <a id="4429" class="Symbol">(</a> <a id="4431" href="ring-theory.semirings.html#7160" class="Function">associative-mul-Semiring</a>
        <a id="4464" class="Symbol">(</a> <a id="4466" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a><a id="4467" class="Symbol">)</a>
        <a id="4477" class="Symbol">(</a> <a id="4479" href="ring-theory.geometric-sequences-semirings.html#3977" class="Bound">a</a><a id="4480" class="Symbol">)</a>
        <a id="4490" class="Symbol">(</a> <a id="4492" href="ring-theory.powers-of-elements-semirings.html#675" class="Function">power-Semiring</a> <a id="4507" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a> <a id="4509" href="ring-theory.geometric-sequences-semirings.html#4336" class="Bound">n</a> <a id="4511" href="ring-theory.geometric-sequences-semirings.html#3979" class="Bound">r</a><a id="4512" class="Symbol">)</a>
        <a id="4522" class="Symbol">(</a> <a id="4524" href="ring-theory.geometric-sequences-semirings.html#3979" class="Bound">r</a><a id="4525" class="Symbol">)))</a>

  <a id="4532" href="ring-theory.geometric-sequences-semirings.html#4532" class="Function">is-geometric-mul-pow-nat-Semiring</a> <a id="4566" class="Symbol">:</a>
    <a id="4572" href="group-theory.arithmetic-sequences-semigroups.html#1966" class="Function">is-arithmetic-sequence-Semigroup</a>
      <a id="4611" class="Symbol">(</a> <a id="4613" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="4647" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a><a id="4648" class="Symbol">)</a>
      <a id="4656" class="Symbol">(</a> <a id="4658" href="ring-theory.geometric-sequences-semirings.html#4011" class="Function">mul-pow-nat-Semiring</a><a id="4678" class="Symbol">)</a>
  <a id="4682" href="ring-theory.geometric-sequences-semirings.html#4532" class="Function">is-geometric-mul-pow-nat-Semiring</a> <a id="4716" class="Symbol">=</a>
    <a id="4722" class="Symbol">(</a> <a id="4724" href="ring-theory.geometric-sequences-semirings.html#3979" class="Bound">r</a> <a id="4726" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4728" href="ring-theory.geometric-sequences-semirings.html#4128" class="Function">is-common-ratio-mul-pow-nat-Semiring</a><a id="4764" class="Symbol">)</a>

  <a id="4769" href="ring-theory.geometric-sequences-semirings.html#4769" class="Function">geometric-mul-pow-nat-Semiring</a> <a id="4800" class="Symbol">:</a> <a id="4802" href="ring-theory.geometric-sequences-semirings.html#1281" class="Function">geometric-sequence-Semiring</a> <a id="4830" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a>
  <a id="4834" href="ring-theory.geometric-sequences-semirings.html#4769" class="Function">geometric-mul-pow-nat-Semiring</a> <a id="4865" class="Symbol">=</a>
    <a id="4871" class="Symbol">(</a> <a id="4873" href="ring-theory.geometric-sequences-semirings.html#4011" class="Function">mul-pow-nat-Semiring</a> <a id="4894" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4896" href="ring-theory.geometric-sequences-semirings.html#4532" class="Function">is-geometric-mul-pow-nat-Semiring</a><a id="4929" class="Symbol">)</a>

  <a id="4934" href="ring-theory.geometric-sequences-semirings.html#4934" class="Function">initial-term-mul-pow-nat-Semiring</a> <a id="4968" class="Symbol">:</a> <a id="4970" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="4984" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a>
  <a id="4988" href="ring-theory.geometric-sequences-semirings.html#4934" class="Function">initial-term-mul-pow-nat-Semiring</a> <a id="5022" class="Symbol">=</a>
    <a id="5028" href="ring-theory.geometric-sequences-semirings.html#2648" class="Function">initial-term-geometric-sequence-Semiring</a>
      <a id="5075" class="Symbol">(</a> <a id="5077" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a><a id="5078" class="Symbol">)</a>
      <a id="5086" class="Symbol">(</a> <a id="5088" href="ring-theory.geometric-sequences-semirings.html#4769" class="Function">geometric-mul-pow-nat-Semiring</a><a id="5118" class="Symbol">)</a>

  <a id="5123" href="ring-theory.geometric-sequences-semirings.html#5123" class="Function">eq-initial-term-mul-pow-nat-Semiring</a> <a id="5160" class="Symbol">:</a>
    <a id="5166" href="ring-theory.geometric-sequences-semirings.html#4934" class="Function">initial-term-mul-pow-nat-Semiring</a> <a id="5200" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="5202" href="ring-theory.geometric-sequences-semirings.html#3977" class="Bound">a</a>
  <a id="5206" href="ring-theory.geometric-sequences-semirings.html#5123" class="Function">eq-initial-term-mul-pow-nat-Semiring</a> <a id="5243" class="Symbol">=</a>
    <a id="5249" href="ring-theory.semirings.html#9527" class="Function">right-unit-law-mul-Semiring</a> <a id="5277" href="ring-theory.geometric-sequences-semirings.html#3960" class="Bound">R</a> <a id="5279" href="ring-theory.geometric-sequences-semirings.html#3977" class="Bound">a</a>
</pre>
## Properties

### Any geometric sequence in a semiring is homotopic to a standard geometric sequence

<pre class="Agda"><a id="5397" class="Keyword">module</a> <a id="5404" href="ring-theory.geometric-sequences-semirings.html#5404" class="Module">_</a>
  <a id="5408" class="Symbol">{</a><a id="5409" href="ring-theory.geometric-sequences-semirings.html#5409" class="Bound">l</a> <a id="5411" class="Symbol">:</a> <a id="5413" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5418" class="Symbol">}</a> <a id="5420" class="Symbol">(</a><a id="5421" href="ring-theory.geometric-sequences-semirings.html#5421" class="Bound">R</a> <a id="5423" class="Symbol">:</a> <a id="5425" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="5434" href="ring-theory.geometric-sequences-semirings.html#5409" class="Bound">l</a><a id="5435" class="Symbol">)</a>
  <a id="5439" class="Symbol">(</a><a id="5440" href="ring-theory.geometric-sequences-semirings.html#5440" class="Bound">u</a> <a id="5442" class="Symbol">:</a> <a id="5444" href="ring-theory.geometric-sequences-semirings.html#1281" class="Function">geometric-sequence-Semiring</a> <a id="5472" href="ring-theory.geometric-sequences-semirings.html#5421" class="Bound">R</a><a id="5473" class="Symbol">)</a>
  <a id="5477" class="Keyword">where</a>

  <a id="5486" href="ring-theory.geometric-sequences-semirings.html#5486" class="Function">htpy-seq-standard-geometric-sequence-Semiring</a> <a id="5532" class="Symbol">:</a>
    <a id="5538" class="Symbol">(</a> <a id="5540" href="ring-theory.geometric-sequences-semirings.html#1517" class="Function">seq-geometric-sequence-Semiring</a> <a id="5572" href="ring-theory.geometric-sequences-semirings.html#5421" class="Bound">R</a>
      <a id="5580" class="Symbol">(</a> <a id="5582" href="ring-theory.geometric-sequences-semirings.html#3134" class="Function">standard-geometric-sequence-Semiring</a> <a id="5619" href="ring-theory.geometric-sequences-semirings.html#5421" class="Bound">R</a>
        <a id="5629" class="Symbol">(</a> <a id="5631" href="ring-theory.geometric-sequences-semirings.html#2648" class="Function">initial-term-geometric-sequence-Semiring</a> <a id="5672" href="ring-theory.geometric-sequences-semirings.html#5421" class="Bound">R</a> <a id="5674" href="ring-theory.geometric-sequences-semirings.html#5440" class="Bound">u</a><a id="5675" class="Symbol">)</a>
        <a id="5685" class="Symbol">(</a> <a id="5687" href="ring-theory.geometric-sequences-semirings.html#2034" class="Function">common-ratio-geometric-sequence-Semiring</a> <a id="5728" href="ring-theory.geometric-sequences-semirings.html#5421" class="Bound">R</a> <a id="5730" href="ring-theory.geometric-sequences-semirings.html#5440" class="Bound">u</a><a id="5731" class="Symbol">)))</a> <a id="5735" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a>
    <a id="5741" class="Symbol">(</a> <a id="5743" href="ring-theory.geometric-sequences-semirings.html#1517" class="Function">seq-geometric-sequence-Semiring</a> <a id="5775" href="ring-theory.geometric-sequences-semirings.html#5421" class="Bound">R</a> <a id="5777" href="ring-theory.geometric-sequences-semirings.html#5440" class="Bound">u</a><a id="5778" class="Symbol">)</a>
  <a id="5782" href="ring-theory.geometric-sequences-semirings.html#5486" class="Function">htpy-seq-standard-geometric-sequence-Semiring</a> <a id="5828" class="Symbol">=</a>
    <a id="5834" href="group-theory.arithmetic-sequences-semigroups.html#5637" class="Function">htpy-seq-standard-arithmetic-sequence-Semigroup</a>
      <a id="5888" class="Symbol">(</a> <a id="5890" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="5924" href="ring-theory.geometric-sequences-semirings.html#5421" class="Bound">R</a><a id="5925" class="Symbol">)</a>
      <a id="5933" class="Symbol">(</a> <a id="5935" href="ring-theory.geometric-sequences-semirings.html#5440" class="Bound">u</a><a id="5936" class="Symbol">)</a>
</pre>
### The nth term of an geometric sequence with initial term `a` and common ratio `r` is `a * rⁿ`

<pre class="Agda"><a id="6049" class="Keyword">module</a> <a id="6056" href="ring-theory.geometric-sequences-semirings.html#6056" class="Module">_</a>
  <a id="6060" class="Symbol">{</a><a id="6061" href="ring-theory.geometric-sequences-semirings.html#6061" class="Bound">l</a> <a id="6063" class="Symbol">:</a> <a id="6065" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6070" class="Symbol">}</a> <a id="6072" class="Symbol">(</a><a id="6073" href="ring-theory.geometric-sequences-semirings.html#6073" class="Bound">R</a> <a id="6075" class="Symbol">:</a> <a id="6077" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="6086" href="ring-theory.geometric-sequences-semirings.html#6061" class="Bound">l</a><a id="6087" class="Symbol">)</a> <a id="6089" class="Symbol">(</a><a id="6090" href="ring-theory.geometric-sequences-semirings.html#6090" class="Bound">a</a> <a id="6092" href="ring-theory.geometric-sequences-semirings.html#6092" class="Bound">r</a> <a id="6094" class="Symbol">:</a> <a id="6096" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="6110" href="ring-theory.geometric-sequences-semirings.html#6073" class="Bound">R</a><a id="6111" class="Symbol">)</a>
  <a id="6115" class="Keyword">where</a>

  <a id="6124" href="ring-theory.geometric-sequences-semirings.html#6124" class="Function">htpy-mul-pow-standard-geometric-sequence-Semiring</a> <a id="6174" class="Symbol">:</a>
    <a id="6180" href="ring-theory.geometric-sequences-semirings.html#4011" class="Function">mul-pow-nat-Semiring</a> <a id="6201" href="ring-theory.geometric-sequences-semirings.html#6073" class="Bound">R</a> <a id="6203" href="ring-theory.geometric-sequences-semirings.html#6090" class="Bound">a</a> <a id="6205" href="ring-theory.geometric-sequences-semirings.html#6092" class="Bound">r</a> <a id="6207" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="6209" href="ring-theory.geometric-sequences-semirings.html#3357" class="Function">seq-standard-geometric-sequence-Semiring</a> <a id="6250" href="ring-theory.geometric-sequences-semirings.html#6073" class="Bound">R</a> <a id="6252" href="ring-theory.geometric-sequences-semirings.html#6090" class="Bound">a</a> <a id="6254" href="ring-theory.geometric-sequences-semirings.html#6092" class="Bound">r</a>
  <a id="6258" href="ring-theory.geometric-sequences-semirings.html#6124" class="Function">htpy-mul-pow-standard-geometric-sequence-Semiring</a> <a id="6308" class="Symbol">=</a>
    <a id="6314" href="group-theory.arithmetic-sequences-semigroups.html#4902" class="Function">htpy-seq-arithmetic-sequence-Semigroup</a>
      <a id="6359" class="Symbol">(</a> <a id="6361" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="6395" href="ring-theory.geometric-sequences-semirings.html#6073" class="Bound">R</a><a id="6396" class="Symbol">)</a>
      <a id="6404" class="Symbol">(</a> <a id="6406" href="ring-theory.geometric-sequences-semirings.html#4769" class="Function">geometric-mul-pow-nat-Semiring</a> <a id="6437" href="ring-theory.geometric-sequences-semirings.html#6073" class="Bound">R</a> <a id="6439" href="ring-theory.geometric-sequences-semirings.html#6090" class="Bound">a</a> <a id="6441" href="ring-theory.geometric-sequences-semirings.html#6092" class="Bound">r</a><a id="6442" class="Symbol">)</a>
      <a id="6450" class="Symbol">(</a> <a id="6452" href="ring-theory.geometric-sequences-semirings.html#3134" class="Function">standard-geometric-sequence-Semiring</a> <a id="6489" href="ring-theory.geometric-sequences-semirings.html#6073" class="Bound">R</a> <a id="6491" href="ring-theory.geometric-sequences-semirings.html#6090" class="Bound">a</a> <a id="6493" href="ring-theory.geometric-sequences-semirings.html#6092" class="Bound">r</a><a id="6494" class="Symbol">)</a>
      <a id="6502" class="Symbol">(</a> <a id="6504" href="ring-theory.geometric-sequences-semirings.html#5123" class="Function">eq-initial-term-mul-pow-nat-Semiring</a> <a id="6541" href="ring-theory.geometric-sequences-semirings.html#6073" class="Bound">R</a> <a id="6543" href="ring-theory.geometric-sequences-semirings.html#6090" class="Bound">a</a> <a id="6545" href="ring-theory.geometric-sequences-semirings.html#6092" class="Bound">r</a><a id="6546" class="Symbol">)</a>
      <a id="6554" class="Symbol">(</a> <a id="6556" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="6560" class="Symbol">)</a>
</pre>
<pre class="Agda"><a id="6575" class="Keyword">module</a> <a id="6582" href="ring-theory.geometric-sequences-semirings.html#6582" class="Module">_</a>
  <a id="6586" class="Symbol">{</a><a id="6587" href="ring-theory.geometric-sequences-semirings.html#6587" class="Bound">l</a> <a id="6589" class="Symbol">:</a> <a id="6591" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6596" class="Symbol">}</a> <a id="6598" class="Symbol">(</a><a id="6599" href="ring-theory.geometric-sequences-semirings.html#6599" class="Bound">R</a> <a id="6601" class="Symbol">:</a> <a id="6603" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="6612" href="ring-theory.geometric-sequences-semirings.html#6587" class="Bound">l</a><a id="6613" class="Symbol">)</a> <a id="6615" class="Symbol">(</a><a id="6616" href="ring-theory.geometric-sequences-semirings.html#6616" class="Bound">u</a> <a id="6618" class="Symbol">:</a> <a id="6620" href="ring-theory.geometric-sequences-semirings.html#1281" class="Function">geometric-sequence-Semiring</a> <a id="6648" href="ring-theory.geometric-sequences-semirings.html#6599" class="Bound">R</a><a id="6649" class="Symbol">)</a>
  <a id="6653" class="Keyword">where</a>

  <a id="6662" href="ring-theory.geometric-sequences-semirings.html#6662" class="Function">htpy-mul-pow-geometric-sequence-Semiring</a> <a id="6703" class="Symbol">:</a>
    <a id="6709" href="ring-theory.geometric-sequences-semirings.html#4011" class="Function">mul-pow-nat-Semiring</a>
      <a id="6736" class="Symbol">(</a> <a id="6738" href="ring-theory.geometric-sequences-semirings.html#6599" class="Bound">R</a><a id="6739" class="Symbol">)</a>
      <a id="6747" class="Symbol">(</a> <a id="6749" href="ring-theory.geometric-sequences-semirings.html#2648" class="Function">initial-term-geometric-sequence-Semiring</a> <a id="6790" href="ring-theory.geometric-sequences-semirings.html#6599" class="Bound">R</a> <a id="6792" href="ring-theory.geometric-sequences-semirings.html#6616" class="Bound">u</a><a id="6793" class="Symbol">)</a>
      <a id="6801" class="Symbol">(</a> <a id="6803" href="ring-theory.geometric-sequences-semirings.html#2034" class="Function">common-ratio-geometric-sequence-Semiring</a> <a id="6844" href="ring-theory.geometric-sequences-semirings.html#6599" class="Bound">R</a> <a id="6846" href="ring-theory.geometric-sequences-semirings.html#6616" class="Bound">u</a><a id="6847" class="Symbol">)</a> <a id="6849" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a>
    <a id="6855" href="ring-theory.geometric-sequences-semirings.html#1517" class="Function">seq-geometric-sequence-Semiring</a> <a id="6887" href="ring-theory.geometric-sequences-semirings.html#6599" class="Bound">R</a> <a id="6889" href="ring-theory.geometric-sequences-semirings.html#6616" class="Bound">u</a>
  <a id="6893" href="ring-theory.geometric-sequences-semirings.html#6662" class="Function">htpy-mul-pow-geometric-sequence-Semiring</a> <a id="6934" href="ring-theory.geometric-sequences-semirings.html#6934" class="Bound">n</a> <a id="6936" class="Symbol">=</a>
    <a id="6942" class="Symbol">(</a> <a id="6944" href="ring-theory.geometric-sequences-semirings.html#6124" class="Function">htpy-mul-pow-standard-geometric-sequence-Semiring</a>
      <a id="7000" class="Symbol">(</a> <a id="7002" href="ring-theory.geometric-sequences-semirings.html#6599" class="Bound">R</a><a id="7003" class="Symbol">)</a>
      <a id="7011" class="Symbol">(</a> <a id="7013" href="ring-theory.geometric-sequences-semirings.html#2648" class="Function">initial-term-geometric-sequence-Semiring</a> <a id="7054" href="ring-theory.geometric-sequences-semirings.html#6599" class="Bound">R</a> <a id="7056" href="ring-theory.geometric-sequences-semirings.html#6616" class="Bound">u</a><a id="7057" class="Symbol">)</a>
      <a id="7065" class="Symbol">(</a> <a id="7067" href="ring-theory.geometric-sequences-semirings.html#2034" class="Function">common-ratio-geometric-sequence-Semiring</a> <a id="7108" href="ring-theory.geometric-sequences-semirings.html#6599" class="Bound">R</a> <a id="7110" href="ring-theory.geometric-sequences-semirings.html#6616" class="Bound">u</a><a id="7111" class="Symbol">)</a>
      <a id="7119" class="Symbol">(</a> <a id="7121" href="ring-theory.geometric-sequences-semirings.html#6934" class="Bound">n</a><a id="7122" class="Symbol">))</a> <a id="7125" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
    <a id="7131" class="Symbol">(</a> <a id="7133" href="group-theory.arithmetic-sequences-semigroups.html#5637" class="Function">htpy-seq-standard-arithmetic-sequence-Semigroup</a>
      <a id="7187" class="Symbol">(</a> <a id="7189" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="7223" href="ring-theory.geometric-sequences-semirings.html#6599" class="Bound">R</a><a id="7224" class="Symbol">)</a>
      <a id="7232" class="Symbol">(</a> <a id="7234" href="ring-theory.geometric-sequences-semirings.html#6616" class="Bound">u</a><a id="7235" class="Symbol">)</a>
      <a id="7243" class="Symbol">(</a> <a id="7245" href="ring-theory.geometric-sequences-semirings.html#6934" class="Bound">n</a><a id="7246" class="Symbol">))</a>
</pre>
### Constant sequences are geometric with common ratio one

<pre class="Agda"><a id="7322" class="Keyword">module</a> <a id="7329" href="ring-theory.geometric-sequences-semirings.html#7329" class="Module">_</a>
  <a id="7333" class="Symbol">{</a><a id="7334" href="ring-theory.geometric-sequences-semirings.html#7334" class="Bound">l</a> <a id="7336" class="Symbol">:</a> <a id="7338" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7343" class="Symbol">}</a> <a id="7345" class="Symbol">(</a><a id="7346" href="ring-theory.geometric-sequences-semirings.html#7346" class="Bound">R</a> <a id="7348" class="Symbol">:</a> <a id="7350" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="7359" href="ring-theory.geometric-sequences-semirings.html#7334" class="Bound">l</a><a id="7360" class="Symbol">)</a> <a id="7362" class="Symbol">(</a><a id="7363" href="ring-theory.geometric-sequences-semirings.html#7363" class="Bound">a</a> <a id="7365" class="Symbol">:</a> <a id="7367" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="7381" href="ring-theory.geometric-sequences-semirings.html#7346" class="Bound">R</a><a id="7382" class="Symbol">)</a>
  <a id="7386" class="Keyword">where</a>

  <a id="7395" href="ring-theory.geometric-sequences-semirings.html#7395" class="Function">one-is-common-ratio-const-sequence-Semiring</a> <a id="7439" class="Symbol">:</a>
    <a id="7445" href="group-theory.arithmetic-sequences-semigroups.html#1788" class="Function">is-common-difference-sequence-Semigroup</a>
      <a id="7491" class="Symbol">(</a> <a id="7493" href="ring-theory.semirings.html#7363" class="Function">multiplicative-semigroup-Semiring</a> <a id="7527" href="ring-theory.geometric-sequences-semirings.html#7346" class="Bound">R</a><a id="7528" class="Symbol">)</a>
      <a id="7536" class="Symbol">(</a> <a id="7538" class="Symbol">λ</a> <a id="7540" href="ring-theory.geometric-sequences-semirings.html#7540" class="Symbol">_</a> <a id="7542" class="Symbol">→</a> <a id="7544" href="ring-theory.geometric-sequences-semirings.html#7363" class="Bound">a</a><a id="7545" class="Symbol">)</a>
      <a id="7553" class="Symbol">(</a> <a id="7555" href="ring-theory.semirings.html#9245" class="Function">one-Semiring</a> <a id="7568" href="ring-theory.geometric-sequences-semirings.html#7346" class="Bound">R</a><a id="7569" class="Symbol">)</a>
  <a id="7573" href="ring-theory.geometric-sequences-semirings.html#7395" class="Function">one-is-common-ratio-const-sequence-Semiring</a> <a id="7617" href="ring-theory.geometric-sequences-semirings.html#7617" class="Bound">n</a> <a id="7619" class="Symbol">=</a>
    <a id="7625" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="7629" class="Symbol">(</a><a id="7630" href="ring-theory.semirings.html#9527" class="Function">right-unit-law-mul-Semiring</a> <a id="7658" href="ring-theory.geometric-sequences-semirings.html#7346" class="Bound">R</a> <a id="7660" href="ring-theory.geometric-sequences-semirings.html#7363" class="Bound">a</a><a id="7661" class="Symbol">)</a>

  <a id="7666" href="ring-theory.geometric-sequences-semirings.html#7666" class="Function">geometric-const-sequence-Semiring</a> <a id="7700" class="Symbol">:</a> <a id="7702" href="ring-theory.geometric-sequences-semirings.html#1281" class="Function">geometric-sequence-Semiring</a> <a id="7730" href="ring-theory.geometric-sequences-semirings.html#7346" class="Bound">R</a>
  <a id="7734" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="7738" href="ring-theory.geometric-sequences-semirings.html#7666" class="Function">geometric-const-sequence-Semiring</a> <a id="7772" class="Symbol">_</a> <a id="7774" class="Symbol">=</a> <a id="7776" href="ring-theory.geometric-sequences-semirings.html#7363" class="Bound">a</a>
  <a id="7780" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="7784" href="ring-theory.geometric-sequences-semirings.html#7666" class="Function">geometric-const-sequence-Semiring</a> <a id="7818" class="Symbol">=</a>
    <a id="7824" class="Symbol">(</a> <a id="7826" href="ring-theory.semirings.html#9245" class="Function">one-Semiring</a> <a id="7839" href="ring-theory.geometric-sequences-semirings.html#7346" class="Bound">R</a> <a id="7841" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="7843" href="ring-theory.geometric-sequences-semirings.html#7395" class="Function">one-is-common-ratio-const-sequence-Semiring</a><a id="7886" class="Symbol">)</a>
</pre>
## External links

- [Geometric progressions](https://en.wikipedia.org/wiki/Geometric_progression)
  at Wikipedia
