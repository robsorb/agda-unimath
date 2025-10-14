# Arithmetic sequences in semirings

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="ring-theory.arithmetic-sequences-semirings.html" class="Module">ring-theory.arithmetic-sequences-semirings</a> <a id="96" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="152" class="Keyword">open</a> <a id="157" class="Keyword">import</a> <a id="164" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="foundation.action-on-identifications-binary-functions.html" class="Module">foundation.action-on-identifications-binary-functions</a>
<a id="272" class="Keyword">open</a> <a id="277" class="Keyword">import</a> <a id="284" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="331" class="Keyword">open</a> <a id="336" class="Keyword">import</a> <a id="343" href="foundation.binary-transport.html" class="Module">foundation.binary-transport</a>
<a id="371" class="Keyword">open</a> <a id="376" class="Keyword">import</a> <a id="383" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="415" class="Keyword">open</a> <a id="420" class="Keyword">import</a> <a id="427" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="449" class="Keyword">open</a> <a id="454" class="Keyword">import</a> <a id="461" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="487" class="Keyword">open</a> <a id="492" class="Keyword">import</a> <a id="499" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="523" class="Keyword">open</a> <a id="528" class="Keyword">import</a> <a id="535" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="551" class="Keyword">open</a> <a id="556" class="Keyword">import</a> <a id="563" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="591" class="Keyword">open</a> <a id="596" class="Keyword">import</a> <a id="603" href="group-theory.arithmetic-sequences-semigroups.html" class="Module">group-theory.arithmetic-sequences-semigroups</a>

<a id="649" class="Keyword">open</a> <a id="654" class="Keyword">import</a> <a id="661" href="lists.sequences.html" class="Module">lists.sequences</a>

<a id="678" class="Keyword">open</a> <a id="683" class="Keyword">import</a> <a id="690" href="ring-theory.semirings.html" class="Module">ring-theory.semirings</a>
</pre>
</details>

## Ideas

An
{{#concept "arithmetic sequence" Disambiguation="in a semiring" Agda=arithmetic-sequence-Semiring}}
in a [semiring](ring-theory.semirings.md) is an
[arithmetic sequence](group-theory.arithmetic-sequences-semigroups.md) in the
semiring's additive [semigroup](group-theory.semigroups.md).

These are the sequences `n ↦ a + n * d` for some elements `a d` in the semiring.

## Definitions

### Arithmetic sequences in semirings

<pre class="Agda"><a id="1175" class="Keyword">module</a> <a id="1182" href="ring-theory.arithmetic-sequences-semirings.html#1182" class="Module">_</a>
  <a id="1186" class="Symbol">{</a><a id="1187" href="ring-theory.arithmetic-sequences-semirings.html#1187" class="Bound">l</a> <a id="1189" class="Symbol">:</a> <a id="1191" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1196" class="Symbol">}</a> <a id="1198" class="Symbol">(</a><a id="1199" href="ring-theory.arithmetic-sequences-semirings.html#1199" class="Bound">R</a> <a id="1201" class="Symbol">:</a> <a id="1203" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="1212" href="ring-theory.arithmetic-sequences-semirings.html#1187" class="Bound">l</a><a id="1213" class="Symbol">)</a>
  <a id="1217" class="Keyword">where</a>

  <a id="1226" href="ring-theory.arithmetic-sequences-semirings.html#1226" class="Function">arithmetic-sequence-Semiring</a> <a id="1255" class="Symbol">:</a> <a id="1257" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1260" href="ring-theory.arithmetic-sequences-semirings.html#1187" class="Bound">l</a>
  <a id="1264" href="ring-theory.arithmetic-sequences-semirings.html#1226" class="Function">arithmetic-sequence-Semiring</a> <a id="1293" class="Symbol">=</a>
    <a id="1299" href="group-theory.arithmetic-sequences-semigroups.html#2216" class="Function">arithmetic-sequence-Semigroup</a>
      <a id="1335" class="Symbol">(</a> <a id="1337" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="1365" href="ring-theory.arithmetic-sequences-semirings.html#1199" class="Bound">R</a><a id="1366" class="Symbol">)</a>

<a id="1369" class="Keyword">module</a> <a id="1376" href="ring-theory.arithmetic-sequences-semirings.html#1376" class="Module">_</a>
  <a id="1380" class="Symbol">{</a><a id="1381" href="ring-theory.arithmetic-sequences-semirings.html#1381" class="Bound">l</a> <a id="1383" class="Symbol">:</a> <a id="1385" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1390" class="Symbol">}</a> <a id="1392" class="Symbol">(</a><a id="1393" href="ring-theory.arithmetic-sequences-semirings.html#1393" class="Bound">R</a> <a id="1395" class="Symbol">:</a> <a id="1397" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="1406" href="ring-theory.arithmetic-sequences-semirings.html#1381" class="Bound">l</a><a id="1407" class="Symbol">)</a>
  <a id="1411" class="Symbol">(</a><a id="1412" href="ring-theory.arithmetic-sequences-semirings.html#1412" class="Bound">u</a> <a id="1414" class="Symbol">:</a> <a id="1416" href="ring-theory.arithmetic-sequences-semirings.html#1226" class="Function">arithmetic-sequence-Semiring</a> <a id="1445" href="ring-theory.arithmetic-sequences-semirings.html#1393" class="Bound">R</a><a id="1446" class="Symbol">)</a>
  <a id="1450" class="Keyword">where</a>

  <a id="1459" href="ring-theory.arithmetic-sequences-semirings.html#1459" class="Function">seq-arithmetic-sequence-Semiring</a> <a id="1492" class="Symbol">:</a> <a id="1494" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1496" class="Symbol">→</a> <a id="1498" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="1512" href="ring-theory.arithmetic-sequences-semirings.html#1393" class="Bound">R</a>
  <a id="1516" href="ring-theory.arithmetic-sequences-semirings.html#1459" class="Function">seq-arithmetic-sequence-Semiring</a> <a id="1549" class="Symbol">=</a>
    <a id="1555" href="group-theory.arithmetic-sequences-semigroups.html#2444" class="Function">seq-arithmetic-sequence-Semigroup</a>
      <a id="1595" class="Symbol">(</a> <a id="1597" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="1625" href="ring-theory.arithmetic-sequences-semirings.html#1393" class="Bound">R</a><a id="1626" class="Symbol">)</a>
      <a id="1634" class="Symbol">(</a> <a id="1636" href="ring-theory.arithmetic-sequences-semirings.html#1412" class="Bound">u</a><a id="1637" class="Symbol">)</a>

  <a id="1642" href="ring-theory.arithmetic-sequences-semirings.html#1642" class="Function">is-arithmetic-seq-arithmetic-sequence-Semiring</a> <a id="1689" class="Symbol">:</a>
    <a id="1695" href="group-theory.arithmetic-sequences-semigroups.html#1966" class="Function">is-arithmetic-sequence-Semigroup</a>
      <a id="1734" class="Symbol">(</a> <a id="1736" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="1764" href="ring-theory.arithmetic-sequences-semirings.html#1393" class="Bound">R</a><a id="1765" class="Symbol">)</a>
      <a id="1773" class="Symbol">(</a> <a id="1775" href="ring-theory.arithmetic-sequences-semirings.html#1459" class="Function">seq-arithmetic-sequence-Semiring</a><a id="1807" class="Symbol">)</a>
  <a id="1811" href="ring-theory.arithmetic-sequences-semirings.html#1642" class="Function">is-arithmetic-seq-arithmetic-sequence-Semiring</a> <a id="1858" class="Symbol">=</a>
    <a id="1864" href="group-theory.arithmetic-sequences-semigroups.html#2548" class="Function">is-arithmetic-seq-arithmetic-sequence-Semigroup</a>
      <a id="1918" class="Symbol">(</a> <a id="1920" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="1948" href="ring-theory.arithmetic-sequences-semirings.html#1393" class="Bound">R</a><a id="1949" class="Symbol">)</a>
      <a id="1957" class="Symbol">(</a> <a id="1959" href="ring-theory.arithmetic-sequences-semirings.html#1412" class="Bound">u</a><a id="1960" class="Symbol">)</a>

  <a id="1965" href="ring-theory.arithmetic-sequences-semirings.html#1965" class="Function">common-difference-arithmetic-sequence-Semiring</a> <a id="2012" class="Symbol">:</a> <a id="2014" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="2028" href="ring-theory.arithmetic-sequences-semirings.html#1393" class="Bound">R</a>
  <a id="2032" href="ring-theory.arithmetic-sequences-semirings.html#1965" class="Function">common-difference-arithmetic-sequence-Semiring</a> <a id="2079" class="Symbol">=</a>
    <a id="2085" href="group-theory.arithmetic-sequences-semigroups.html#2732" class="Function">common-difference-arithmetic-sequence-Semigroup</a>
      <a id="2139" class="Symbol">(</a> <a id="2141" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="2169" href="ring-theory.arithmetic-sequences-semirings.html#1393" class="Bound">R</a><a id="2170" class="Symbol">)</a>
      <a id="2178" class="Symbol">(</a> <a id="2180" href="ring-theory.arithmetic-sequences-semirings.html#1412" class="Bound">u</a><a id="2181" class="Symbol">)</a>

  <a id="2186" href="ring-theory.arithmetic-sequences-semirings.html#2186" class="Function">is-common-difference-arithmetic-sequence-Semiring</a> <a id="2236" class="Symbol">:</a>
    <a id="2242" class="Symbol">(</a> <a id="2244" href="ring-theory.arithmetic-sequences-semirings.html#2244" class="Bound">n</a> <a id="2246" class="Symbol">:</a> <a id="2248" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2249" class="Symbol">)</a> <a id="2251" class="Symbol">→</a>
    <a id="2257" class="Symbol">(</a> <a id="2259" href="ring-theory.arithmetic-sequences-semirings.html#1459" class="Function">seq-arithmetic-sequence-Semiring</a> <a id="2292" class="Symbol">(</a><a id="2293" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2300" href="ring-theory.arithmetic-sequences-semirings.html#2244" class="Bound">n</a><a id="2301" class="Symbol">))</a> <a id="2304" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="2310" class="Symbol">(</a> <a id="2312" href="ring-theory.semirings.html#3615" class="Function">add-Semiring</a>
      <a id="2331" class="Symbol">(</a> <a id="2333" href="ring-theory.arithmetic-sequences-semirings.html#1393" class="Bound">R</a><a id="2334" class="Symbol">)</a>
      <a id="2342" class="Symbol">(</a> <a id="2344" href="ring-theory.arithmetic-sequences-semirings.html#1459" class="Function">seq-arithmetic-sequence-Semiring</a> <a id="2377" href="ring-theory.arithmetic-sequences-semirings.html#2244" class="Bound">n</a><a id="2378" class="Symbol">)</a>
      <a id="2386" class="Symbol">(</a> <a id="2388" href="ring-theory.arithmetic-sequences-semirings.html#1965" class="Function">common-difference-arithmetic-sequence-Semiring</a><a id="2434" class="Symbol">))</a>
  <a id="2439" href="ring-theory.arithmetic-sequences-semirings.html#2186" class="Function">is-common-difference-arithmetic-sequence-Semiring</a> <a id="2489" class="Symbol">=</a>
    <a id="2495" href="group-theory.arithmetic-sequences-semigroups.html#2910" class="Function">is-common-difference-arithmetic-sequence-Semigroup</a>
      <a id="2552" class="Symbol">(</a> <a id="2554" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="2582" href="ring-theory.arithmetic-sequences-semirings.html#1393" class="Bound">R</a><a id="2583" class="Symbol">)</a>
      <a id="2591" class="Symbol">(</a> <a id="2593" href="ring-theory.arithmetic-sequences-semirings.html#1412" class="Bound">u</a><a id="2594" class="Symbol">)</a>

  <a id="2599" href="ring-theory.arithmetic-sequences-semirings.html#2599" class="Function">initial-term-arithmetic-sequence-Semiring</a> <a id="2641" class="Symbol">:</a> <a id="2643" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="2657" href="ring-theory.arithmetic-sequences-semirings.html#1393" class="Bound">R</a>
  <a id="2661" href="ring-theory.arithmetic-sequences-semirings.html#2599" class="Function">initial-term-arithmetic-sequence-Semiring</a> <a id="2703" class="Symbol">=</a>
    <a id="2709" href="group-theory.arithmetic-sequences-semigroups.html#3217" class="Function">initial-term-arithmetic-sequence-Semigroup</a>
      <a id="2758" class="Symbol">(</a> <a id="2760" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="2788" href="ring-theory.arithmetic-sequences-semirings.html#1393" class="Bound">R</a><a id="2789" class="Symbol">)</a>
      <a id="2797" class="Symbol">(</a> <a id="2799" href="ring-theory.arithmetic-sequences-semirings.html#1412" class="Bound">u</a><a id="2800" class="Symbol">)</a>
</pre>
### The standard arithmetic sequences in a semiring

The standard arithmetic sequence with initial term `a` and common difference `d`
is the sequence `u` defined by:

- `u₀ = a`
- `uₙ₊₁ = uₙ + d`

<pre class="Agda"><a id="3012" class="Keyword">module</a> <a id="3019" href="ring-theory.arithmetic-sequences-semirings.html#3019" class="Module">_</a>
  <a id="3023" class="Symbol">{</a><a id="3024" href="ring-theory.arithmetic-sequences-semirings.html#3024" class="Bound">l</a> <a id="3026" class="Symbol">:</a> <a id="3028" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3033" class="Symbol">}</a> <a id="3035" class="Symbol">(</a><a id="3036" href="ring-theory.arithmetic-sequences-semirings.html#3036" class="Bound">R</a> <a id="3038" class="Symbol">:</a> <a id="3040" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="3049" href="ring-theory.arithmetic-sequences-semirings.html#3024" class="Bound">l</a><a id="3050" class="Symbol">)</a> <a id="3052" class="Symbol">(</a><a id="3053" href="ring-theory.arithmetic-sequences-semirings.html#3053" class="Bound">a</a> <a id="3055" href="ring-theory.arithmetic-sequences-semirings.html#3055" class="Bound">d</a> <a id="3057" class="Symbol">:</a> <a id="3059" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="3073" href="ring-theory.arithmetic-sequences-semirings.html#3036" class="Bound">R</a><a id="3074" class="Symbol">)</a>
  <a id="3078" class="Keyword">where</a>

  <a id="3087" href="ring-theory.arithmetic-sequences-semirings.html#3087" class="Function">standard-arithmetic-sequence-Semiring</a> <a id="3125" class="Symbol">:</a> <a id="3127" href="ring-theory.arithmetic-sequences-semirings.html#1226" class="Function">arithmetic-sequence-Semiring</a> <a id="3156" href="ring-theory.arithmetic-sequences-semirings.html#3036" class="Bound">R</a>
  <a id="3160" href="ring-theory.arithmetic-sequences-semirings.html#3087" class="Function">standard-arithmetic-sequence-Semiring</a> <a id="3198" class="Symbol">=</a>
    <a id="3204" href="group-theory.arithmetic-sequences-semigroups.html#4169" class="Function">standard-arithmetic-sequence-Semigroup</a>
      <a id="3249" class="Symbol">(</a> <a id="3251" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="3279" href="ring-theory.arithmetic-sequences-semirings.html#3036" class="Bound">R</a><a id="3280" class="Symbol">)</a>
      <a id="3288" class="Symbol">(</a> <a id="3290" href="ring-theory.arithmetic-sequences-semirings.html#3053" class="Bound">a</a><a id="3291" class="Symbol">)</a>
      <a id="3299" class="Symbol">(</a> <a id="3301" href="ring-theory.arithmetic-sequences-semirings.html#3055" class="Bound">d</a><a id="3302" class="Symbol">)</a>

  <a id="3307" href="ring-theory.arithmetic-sequences-semirings.html#3307" class="Function">seq-standard-arithmetic-sequence-Semiring</a> <a id="3349" class="Symbol">:</a> <a id="3351" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="3353" class="Symbol">→</a> <a id="3355" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="3369" href="ring-theory.arithmetic-sequences-semirings.html#3036" class="Bound">R</a>
  <a id="3373" href="ring-theory.arithmetic-sequences-semirings.html#3307" class="Function">seq-standard-arithmetic-sequence-Semiring</a> <a id="3415" class="Symbol">=</a>
    <a id="3421" href="ring-theory.arithmetic-sequences-semirings.html#1459" class="Function">seq-arithmetic-sequence-Semiring</a> <a id="3454" href="ring-theory.arithmetic-sequences-semirings.html#3036" class="Bound">R</a>
      <a id="3462" href="ring-theory.arithmetic-sequences-semirings.html#3087" class="Function">standard-arithmetic-sequence-Semiring</a>

  <a id="3503" href="ring-theory.arithmetic-sequences-semirings.html#3503" class="Function">is-arithmetic-standard-arithmetic-sequence-Semiring</a> <a id="3555" class="Symbol">:</a>
    <a id="3561" href="group-theory.arithmetic-sequences-semigroups.html#1966" class="Function">is-arithmetic-sequence-Semigroup</a>
      <a id="3600" class="Symbol">(</a> <a id="3602" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="3630" href="ring-theory.arithmetic-sequences-semirings.html#3036" class="Bound">R</a><a id="3631" class="Symbol">)</a>
      <a id="3639" class="Symbol">(</a> <a id="3641" href="ring-theory.arithmetic-sequences-semirings.html#3307" class="Function">seq-standard-arithmetic-sequence-Semiring</a><a id="3682" class="Symbol">)</a>
  <a id="3686" href="ring-theory.arithmetic-sequences-semirings.html#3503" class="Function">is-arithmetic-standard-arithmetic-sequence-Semiring</a> <a id="3738" class="Symbol">=</a>
    <a id="3744" href="ring-theory.arithmetic-sequences-semirings.html#1642" class="Function">is-arithmetic-seq-arithmetic-sequence-Semiring</a> <a id="3791" href="ring-theory.arithmetic-sequences-semirings.html#3036" class="Bound">R</a>
      <a id="3799" href="ring-theory.arithmetic-sequences-semirings.html#3087" class="Function">standard-arithmetic-sequence-Semiring</a>
</pre>
### The arithmetic sequences `n ↦ a + n * d`

<pre class="Agda"><a id="3896" class="Keyword">module</a> <a id="3903" href="ring-theory.arithmetic-sequences-semirings.html#3903" class="Module">_</a>
  <a id="3907" class="Symbol">{</a><a id="3908" href="ring-theory.arithmetic-sequences-semirings.html#3908" class="Bound">l</a> <a id="3910" class="Symbol">:</a> <a id="3912" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3917" class="Symbol">}</a> <a id="3919" class="Symbol">(</a><a id="3920" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a> <a id="3922" class="Symbol">:</a> <a id="3924" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="3933" href="ring-theory.arithmetic-sequences-semirings.html#3908" class="Bound">l</a><a id="3934" class="Symbol">)</a> <a id="3936" class="Symbol">(</a><a id="3937" href="ring-theory.arithmetic-sequences-semirings.html#3937" class="Bound">a</a> <a id="3939" href="ring-theory.arithmetic-sequences-semirings.html#3939" class="Bound">d</a> <a id="3941" class="Symbol">:</a> <a id="3943" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="3957" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a><a id="3958" class="Symbol">)</a>
  <a id="3962" class="Keyword">where</a>

  <a id="3971" href="ring-theory.arithmetic-sequences-semirings.html#3971" class="Function">add-mul-nat-Semiring</a> <a id="3992" class="Symbol">:</a> <a id="3994" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="3996" class="Symbol">→</a> <a id="3998" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="4012" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a>
  <a id="4016" href="ring-theory.arithmetic-sequences-semirings.html#3971" class="Function">add-mul-nat-Semiring</a> <a id="4037" href="ring-theory.arithmetic-sequences-semirings.html#4037" class="Bound">n</a> <a id="4039" class="Symbol">=</a>
    <a id="4045" href="ring-theory.semirings.html#3615" class="Function">add-Semiring</a> <a id="4058" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a> <a id="4060" href="ring-theory.arithmetic-sequences-semirings.html#3937" class="Bound">a</a> <a id="4062" class="Symbol">(</a><a id="4063" href="ring-theory.semirings.html#9846" class="Function">mul-nat-scalar-Semiring</a> <a id="4087" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a> <a id="4089" href="ring-theory.arithmetic-sequences-semirings.html#4037" class="Bound">n</a> <a id="4091" href="ring-theory.arithmetic-sequences-semirings.html#3939" class="Bound">d</a><a id="4092" class="Symbol">)</a>

  <a id="4097" href="ring-theory.arithmetic-sequences-semirings.html#4097" class="Function">is-common-difference-add-mul-nat-Semiring</a> <a id="4139" class="Symbol">:</a>
    <a id="4145" href="group-theory.arithmetic-sequences-semigroups.html#1788" class="Function">is-common-difference-sequence-Semigroup</a>
      <a id="4191" class="Symbol">(</a> <a id="4193" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="4221" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a><a id="4222" class="Symbol">)</a>
      <a id="4230" class="Symbol">(</a> <a id="4232" href="ring-theory.arithmetic-sequences-semirings.html#3971" class="Function">add-mul-nat-Semiring</a><a id="4252" class="Symbol">)</a>
      <a id="4260" class="Symbol">(</a> <a id="4262" href="ring-theory.arithmetic-sequences-semirings.html#3939" class="Bound">d</a><a id="4263" class="Symbol">)</a>
  <a id="4267" href="ring-theory.arithmetic-sequences-semirings.html#4097" class="Function">is-common-difference-add-mul-nat-Semiring</a> <a id="4309" href="ring-theory.arithmetic-sequences-semirings.html#4309" class="Bound">n</a> <a id="4311" class="Symbol">=</a>
    <a id="4317" href="foundation-core.identity-types.html#6358" class="Function">inv</a>
      <a id="4327" class="Symbol">(</a> <a id="4329" href="ring-theory.semirings.html#4136" class="Function">associative-add-Semiring</a>
        <a id="4362" class="Symbol">(</a> <a id="4364" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a><a id="4365" class="Symbol">)</a>
        <a id="4375" class="Symbol">(</a> <a id="4377" href="ring-theory.arithmetic-sequences-semirings.html#3937" class="Bound">a</a><a id="4378" class="Symbol">)</a>
        <a id="4388" class="Symbol">(</a> <a id="4390" href="ring-theory.semirings.html#9846" class="Function">mul-nat-scalar-Semiring</a> <a id="4414" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a> <a id="4416" href="ring-theory.arithmetic-sequences-semirings.html#4309" class="Bound">n</a> <a id="4418" href="ring-theory.arithmetic-sequences-semirings.html#3939" class="Bound">d</a><a id="4419" class="Symbol">)</a>
        <a id="4429" class="Symbol">(</a> <a id="4431" href="ring-theory.arithmetic-sequences-semirings.html#3939" class="Bound">d</a><a id="4432" class="Symbol">))</a>

  <a id="4438" href="ring-theory.arithmetic-sequences-semirings.html#4438" class="Function">is-arithmetic-add-mul-nat-Semiring</a> <a id="4473" class="Symbol">:</a>
    <a id="4479" href="group-theory.arithmetic-sequences-semigroups.html#1966" class="Function">is-arithmetic-sequence-Semigroup</a>
      <a id="4518" class="Symbol">(</a> <a id="4520" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="4548" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a><a id="4549" class="Symbol">)</a>
      <a id="4557" class="Symbol">(</a> <a id="4559" href="ring-theory.arithmetic-sequences-semirings.html#3971" class="Function">add-mul-nat-Semiring</a><a id="4579" class="Symbol">)</a>
  <a id="4583" href="ring-theory.arithmetic-sequences-semirings.html#4438" class="Function">is-arithmetic-add-mul-nat-Semiring</a> <a id="4618" class="Symbol">=</a>
    <a id="4624" class="Symbol">(</a> <a id="4626" href="ring-theory.arithmetic-sequences-semirings.html#3939" class="Bound">d</a> <a id="4628" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4630" href="ring-theory.arithmetic-sequences-semirings.html#4097" class="Function">is-common-difference-add-mul-nat-Semiring</a><a id="4671" class="Symbol">)</a>

  <a id="4676" href="ring-theory.arithmetic-sequences-semirings.html#4676" class="Function">arithmetic-add-mul-nat-Semiring</a> <a id="4708" class="Symbol">:</a> <a id="4710" href="ring-theory.arithmetic-sequences-semirings.html#1226" class="Function">arithmetic-sequence-Semiring</a> <a id="4739" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a>
  <a id="4743" href="ring-theory.arithmetic-sequences-semirings.html#4676" class="Function">arithmetic-add-mul-nat-Semiring</a> <a id="4775" class="Symbol">=</a>
    <a id="4781" class="Symbol">(</a> <a id="4783" href="ring-theory.arithmetic-sequences-semirings.html#3971" class="Function">add-mul-nat-Semiring</a> <a id="4804" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4806" href="ring-theory.arithmetic-sequences-semirings.html#4438" class="Function">is-arithmetic-add-mul-nat-Semiring</a><a id="4840" class="Symbol">)</a>

  <a id="4845" href="ring-theory.arithmetic-sequences-semirings.html#4845" class="Function">initial-term-add-mul-nat-Semiring</a> <a id="4879" class="Symbol">:</a> <a id="4881" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="4895" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a>
  <a id="4899" href="ring-theory.arithmetic-sequences-semirings.html#4845" class="Function">initial-term-add-mul-nat-Semiring</a> <a id="4933" class="Symbol">=</a>
    <a id="4939" href="ring-theory.arithmetic-sequences-semirings.html#2599" class="Function">initial-term-arithmetic-sequence-Semiring</a>
      <a id="4987" class="Symbol">(</a> <a id="4989" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a><a id="4990" class="Symbol">)</a>
      <a id="4998" class="Symbol">(</a> <a id="5000" href="ring-theory.arithmetic-sequences-semirings.html#4676" class="Function">arithmetic-add-mul-nat-Semiring</a><a id="5031" class="Symbol">)</a>

  <a id="5036" href="ring-theory.arithmetic-sequences-semirings.html#5036" class="Function">eq-initial-term-add-mul-nat-Semiring</a> <a id="5073" class="Symbol">:</a>
    <a id="5079" href="ring-theory.arithmetic-sequences-semirings.html#4845" class="Function">initial-term-add-mul-nat-Semiring</a> <a id="5113" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="5115" href="ring-theory.arithmetic-sequences-semirings.html#3937" class="Bound">a</a>
  <a id="5119" href="ring-theory.arithmetic-sequences-semirings.html#5036" class="Function">eq-initial-term-add-mul-nat-Semiring</a> <a id="5156" class="Symbol">=</a>
    <a id="5162" class="Symbol">(</a> <a id="5164" class="Symbol">(</a> <a id="5166" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
        <a id="5177" class="Symbol">(</a> <a id="5179" href="ring-theory.semirings.html#3615" class="Function">add-Semiring</a> <a id="5192" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a> <a id="5194" href="ring-theory.arithmetic-sequences-semirings.html#3937" class="Bound">a</a><a id="5195" class="Symbol">)</a>
        <a id="5205" class="Symbol">(</a> <a id="5207" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="5211" class="Symbol">(</a><a id="5212" href="ring-theory.semirings.html#10289" class="Function">left-zero-law-mul-nat-scalar-Semiring</a> <a id="5250" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a> <a id="5252" href="ring-theory.arithmetic-sequences-semirings.html#3939" class="Bound">d</a><a id="5253" class="Symbol">)))</a> <a id="5257" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
    <a id="5263" class="Symbol">(</a> <a id="5265" href="ring-theory.semirings.html#6305" class="Function">right-unit-law-add-Semiring</a> <a id="5293" href="ring-theory.arithmetic-sequences-semirings.html#3920" class="Bound">R</a> <a id="5295" href="ring-theory.arithmetic-sequences-semirings.html#3937" class="Bound">a</a><a id="5296" class="Symbol">))</a>
</pre>
## Properties

### Any arithmetic sequence in a semiring is homotopic to a standard arithmetic sequence

<pre class="Agda"><a id="5417" class="Keyword">module</a> <a id="5424" href="ring-theory.arithmetic-sequences-semirings.html#5424" class="Module">_</a>
  <a id="5428" class="Symbol">{</a><a id="5429" href="ring-theory.arithmetic-sequences-semirings.html#5429" class="Bound">l</a> <a id="5431" class="Symbol">:</a> <a id="5433" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5438" class="Symbol">}</a> <a id="5440" class="Symbol">(</a><a id="5441" href="ring-theory.arithmetic-sequences-semirings.html#5441" class="Bound">R</a> <a id="5443" class="Symbol">:</a> <a id="5445" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="5454" href="ring-theory.arithmetic-sequences-semirings.html#5429" class="Bound">l</a><a id="5455" class="Symbol">)</a>
  <a id="5459" class="Symbol">(</a><a id="5460" href="ring-theory.arithmetic-sequences-semirings.html#5460" class="Bound">u</a> <a id="5462" class="Symbol">:</a> <a id="5464" href="ring-theory.arithmetic-sequences-semirings.html#1226" class="Function">arithmetic-sequence-Semiring</a> <a id="5493" href="ring-theory.arithmetic-sequences-semirings.html#5441" class="Bound">R</a><a id="5494" class="Symbol">)</a>
  <a id="5498" class="Keyword">where</a>

  <a id="5507" href="ring-theory.arithmetic-sequences-semirings.html#5507" class="Function">htpy-seq-standard-arithmetic-sequence-Semiring</a> <a id="5554" class="Symbol">:</a>
    <a id="5560" class="Symbol">(</a> <a id="5562" href="ring-theory.arithmetic-sequences-semirings.html#1459" class="Function">seq-arithmetic-sequence-Semiring</a> <a id="5595" href="ring-theory.arithmetic-sequences-semirings.html#5441" class="Bound">R</a>
      <a id="5603" class="Symbol">(</a> <a id="5605" href="ring-theory.arithmetic-sequences-semirings.html#3087" class="Function">standard-arithmetic-sequence-Semiring</a> <a id="5643" href="ring-theory.arithmetic-sequences-semirings.html#5441" class="Bound">R</a>
        <a id="5653" class="Symbol">(</a> <a id="5655" href="ring-theory.arithmetic-sequences-semirings.html#2599" class="Function">initial-term-arithmetic-sequence-Semiring</a> <a id="5697" href="ring-theory.arithmetic-sequences-semirings.html#5441" class="Bound">R</a> <a id="5699" href="ring-theory.arithmetic-sequences-semirings.html#5460" class="Bound">u</a><a id="5700" class="Symbol">)</a>
        <a id="5710" class="Symbol">(</a> <a id="5712" href="ring-theory.arithmetic-sequences-semirings.html#1965" class="Function">common-difference-arithmetic-sequence-Semiring</a> <a id="5759" href="ring-theory.arithmetic-sequences-semirings.html#5441" class="Bound">R</a> <a id="5761" href="ring-theory.arithmetic-sequences-semirings.html#5460" class="Bound">u</a><a id="5762" class="Symbol">)))</a> <a id="5766" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a>
    <a id="5772" class="Symbol">(</a> <a id="5774" href="ring-theory.arithmetic-sequences-semirings.html#1459" class="Function">seq-arithmetic-sequence-Semiring</a> <a id="5807" href="ring-theory.arithmetic-sequences-semirings.html#5441" class="Bound">R</a> <a id="5809" href="ring-theory.arithmetic-sequences-semirings.html#5460" class="Bound">u</a><a id="5810" class="Symbol">)</a>
  <a id="5814" href="ring-theory.arithmetic-sequences-semirings.html#5507" class="Function">htpy-seq-standard-arithmetic-sequence-Semiring</a> <a id="5861" class="Symbol">=</a>
    <a id="5867" href="group-theory.arithmetic-sequences-semigroups.html#5637" class="Function">htpy-seq-standard-arithmetic-sequence-Semigroup</a>
      <a id="5921" class="Symbol">(</a> <a id="5923" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="5951" href="ring-theory.arithmetic-sequences-semirings.html#5441" class="Bound">R</a><a id="5952" class="Symbol">)</a>
      <a id="5960" class="Symbol">(</a> <a id="5962" href="ring-theory.arithmetic-sequences-semirings.html#5460" class="Bound">u</a><a id="5963" class="Symbol">)</a>
</pre>
### The nth term of an arithmetic sequence with initial term `a` and common difference `d` is `a + n * d`

<pre class="Agda"><a id="6085" class="Keyword">module</a> <a id="6092" href="ring-theory.arithmetic-sequences-semirings.html#6092" class="Module">_</a>
  <a id="6096" class="Symbol">{</a><a id="6097" href="ring-theory.arithmetic-sequences-semirings.html#6097" class="Bound">l</a> <a id="6099" class="Symbol">:</a> <a id="6101" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6106" class="Symbol">}</a> <a id="6108" class="Symbol">(</a><a id="6109" href="ring-theory.arithmetic-sequences-semirings.html#6109" class="Bound">R</a> <a id="6111" class="Symbol">:</a> <a id="6113" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="6122" href="ring-theory.arithmetic-sequences-semirings.html#6097" class="Bound">l</a><a id="6123" class="Symbol">)</a> <a id="6125" class="Symbol">(</a><a id="6126" href="ring-theory.arithmetic-sequences-semirings.html#6126" class="Bound">a</a> <a id="6128" href="ring-theory.arithmetic-sequences-semirings.html#6128" class="Bound">d</a> <a id="6130" class="Symbol">:</a> <a id="6132" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="6146" href="ring-theory.arithmetic-sequences-semirings.html#6109" class="Bound">R</a><a id="6147" class="Symbol">)</a>
  <a id="6151" class="Keyword">where</a>

  <a id="6160" href="ring-theory.arithmetic-sequences-semirings.html#6160" class="Function">htpy-add-mul-standard-arithmetic-sequence-Semiring</a> <a id="6211" class="Symbol">:</a>
    <a id="6217" href="ring-theory.arithmetic-sequences-semirings.html#3971" class="Function">add-mul-nat-Semiring</a> <a id="6238" href="ring-theory.arithmetic-sequences-semirings.html#6109" class="Bound">R</a> <a id="6240" href="ring-theory.arithmetic-sequences-semirings.html#6126" class="Bound">a</a> <a id="6242" href="ring-theory.arithmetic-sequences-semirings.html#6128" class="Bound">d</a> <a id="6244" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="6246" href="ring-theory.arithmetic-sequences-semirings.html#3307" class="Function">seq-standard-arithmetic-sequence-Semiring</a> <a id="6288" href="ring-theory.arithmetic-sequences-semirings.html#6109" class="Bound">R</a> <a id="6290" href="ring-theory.arithmetic-sequences-semirings.html#6126" class="Bound">a</a> <a id="6292" href="ring-theory.arithmetic-sequences-semirings.html#6128" class="Bound">d</a>
  <a id="6296" href="ring-theory.arithmetic-sequences-semirings.html#6160" class="Function">htpy-add-mul-standard-arithmetic-sequence-Semiring</a> <a id="6347" class="Symbol">=</a>
    <a id="6353" href="group-theory.arithmetic-sequences-semigroups.html#4902" class="Function">htpy-seq-arithmetic-sequence-Semigroup</a>
      <a id="6398" class="Symbol">(</a> <a id="6400" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="6428" href="ring-theory.arithmetic-sequences-semirings.html#6109" class="Bound">R</a><a id="6429" class="Symbol">)</a>
      <a id="6437" class="Symbol">(</a> <a id="6439" href="ring-theory.arithmetic-sequences-semirings.html#4676" class="Function">arithmetic-add-mul-nat-Semiring</a> <a id="6471" href="ring-theory.arithmetic-sequences-semirings.html#6109" class="Bound">R</a> <a id="6473" href="ring-theory.arithmetic-sequences-semirings.html#6126" class="Bound">a</a> <a id="6475" href="ring-theory.arithmetic-sequences-semirings.html#6128" class="Bound">d</a><a id="6476" class="Symbol">)</a>
      <a id="6484" class="Symbol">(</a> <a id="6486" href="ring-theory.arithmetic-sequences-semirings.html#3087" class="Function">standard-arithmetic-sequence-Semiring</a> <a id="6524" href="ring-theory.arithmetic-sequences-semirings.html#6109" class="Bound">R</a> <a id="6526" href="ring-theory.arithmetic-sequences-semirings.html#6126" class="Bound">a</a> <a id="6528" href="ring-theory.arithmetic-sequences-semirings.html#6128" class="Bound">d</a><a id="6529" class="Symbol">)</a>
      <a id="6537" class="Symbol">(</a> <a id="6539" href="ring-theory.arithmetic-sequences-semirings.html#5036" class="Function">eq-initial-term-add-mul-nat-Semiring</a> <a id="6576" href="ring-theory.arithmetic-sequences-semirings.html#6109" class="Bound">R</a> <a id="6578" href="ring-theory.arithmetic-sequences-semirings.html#6126" class="Bound">a</a> <a id="6580" href="ring-theory.arithmetic-sequences-semirings.html#6128" class="Bound">d</a><a id="6581" class="Symbol">)</a>
      <a id="6589" class="Symbol">(</a> <a id="6591" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="6595" class="Symbol">)</a>
</pre>
<pre class="Agda"><a id="6610" class="Keyword">module</a> <a id="6617" href="ring-theory.arithmetic-sequences-semirings.html#6617" class="Module">_</a>
  <a id="6621" class="Symbol">{</a><a id="6622" href="ring-theory.arithmetic-sequences-semirings.html#6622" class="Bound">l</a> <a id="6624" class="Symbol">:</a> <a id="6626" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6631" class="Symbol">}</a> <a id="6633" class="Symbol">(</a><a id="6634" href="ring-theory.arithmetic-sequences-semirings.html#6634" class="Bound">R</a> <a id="6636" class="Symbol">:</a> <a id="6638" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="6647" href="ring-theory.arithmetic-sequences-semirings.html#6622" class="Bound">l</a><a id="6648" class="Symbol">)</a> <a id="6650" class="Symbol">(</a><a id="6651" href="ring-theory.arithmetic-sequences-semirings.html#6651" class="Bound">u</a> <a id="6653" class="Symbol">:</a> <a id="6655" href="ring-theory.arithmetic-sequences-semirings.html#1226" class="Function">arithmetic-sequence-Semiring</a> <a id="6684" href="ring-theory.arithmetic-sequences-semirings.html#6634" class="Bound">R</a><a id="6685" class="Symbol">)</a>
  <a id="6689" class="Keyword">where</a>

  <a id="6698" href="ring-theory.arithmetic-sequences-semirings.html#6698" class="Function">htpy-add-mul-arithmetic-sequence-Semiring</a> <a id="6740" class="Symbol">:</a>
    <a id="6746" href="ring-theory.arithmetic-sequences-semirings.html#3971" class="Function">add-mul-nat-Semiring</a>
      <a id="6773" class="Symbol">(</a> <a id="6775" href="ring-theory.arithmetic-sequences-semirings.html#6634" class="Bound">R</a><a id="6776" class="Symbol">)</a>
      <a id="6784" class="Symbol">(</a> <a id="6786" href="ring-theory.arithmetic-sequences-semirings.html#2599" class="Function">initial-term-arithmetic-sequence-Semiring</a> <a id="6828" href="ring-theory.arithmetic-sequences-semirings.html#6634" class="Bound">R</a> <a id="6830" href="ring-theory.arithmetic-sequences-semirings.html#6651" class="Bound">u</a><a id="6831" class="Symbol">)</a>
      <a id="6839" class="Symbol">(</a> <a id="6841" href="ring-theory.arithmetic-sequences-semirings.html#1965" class="Function">common-difference-arithmetic-sequence-Semiring</a> <a id="6888" href="ring-theory.arithmetic-sequences-semirings.html#6634" class="Bound">R</a> <a id="6890" href="ring-theory.arithmetic-sequences-semirings.html#6651" class="Bound">u</a><a id="6891" class="Symbol">)</a> <a id="6893" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a>
    <a id="6899" href="ring-theory.arithmetic-sequences-semirings.html#1459" class="Function">seq-arithmetic-sequence-Semiring</a> <a id="6932" href="ring-theory.arithmetic-sequences-semirings.html#6634" class="Bound">R</a> <a id="6934" href="ring-theory.arithmetic-sequences-semirings.html#6651" class="Bound">u</a>
  <a id="6938" href="ring-theory.arithmetic-sequences-semirings.html#6698" class="Function">htpy-add-mul-arithmetic-sequence-Semiring</a> <a id="6980" href="ring-theory.arithmetic-sequences-semirings.html#6980" class="Bound">n</a> <a id="6982" class="Symbol">=</a>
    <a id="6988" class="Symbol">(</a> <a id="6990" href="ring-theory.arithmetic-sequences-semirings.html#6160" class="Function">htpy-add-mul-standard-arithmetic-sequence-Semiring</a>
      <a id="7047" class="Symbol">(</a> <a id="7049" href="ring-theory.arithmetic-sequences-semirings.html#6634" class="Bound">R</a><a id="7050" class="Symbol">)</a>
      <a id="7058" class="Symbol">(</a> <a id="7060" href="ring-theory.arithmetic-sequences-semirings.html#2599" class="Function">initial-term-arithmetic-sequence-Semiring</a> <a id="7102" href="ring-theory.arithmetic-sequences-semirings.html#6634" class="Bound">R</a> <a id="7104" href="ring-theory.arithmetic-sequences-semirings.html#6651" class="Bound">u</a><a id="7105" class="Symbol">)</a>
      <a id="7113" class="Symbol">(</a> <a id="7115" href="ring-theory.arithmetic-sequences-semirings.html#1965" class="Function">common-difference-arithmetic-sequence-Semiring</a> <a id="7162" href="ring-theory.arithmetic-sequences-semirings.html#6634" class="Bound">R</a> <a id="7164" href="ring-theory.arithmetic-sequences-semirings.html#6651" class="Bound">u</a><a id="7165" class="Symbol">)</a>
      <a id="7173" class="Symbol">(</a> <a id="7175" href="ring-theory.arithmetic-sequences-semirings.html#6980" class="Bound">n</a><a id="7176" class="Symbol">))</a> <a id="7179" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
    <a id="7185" class="Symbol">(</a> <a id="7187" href="group-theory.arithmetic-sequences-semigroups.html#5637" class="Function">htpy-seq-standard-arithmetic-sequence-Semigroup</a>
      <a id="7241" class="Symbol">(</a> <a id="7243" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="7271" href="ring-theory.arithmetic-sequences-semirings.html#6634" class="Bound">R</a><a id="7272" class="Symbol">)</a>
      <a id="7280" class="Symbol">(</a> <a id="7282" href="ring-theory.arithmetic-sequences-semirings.html#6651" class="Bound">u</a><a id="7283" class="Symbol">)</a>
      <a id="7291" class="Symbol">(</a> <a id="7293" href="ring-theory.arithmetic-sequences-semirings.html#6980" class="Bound">n</a><a id="7294" class="Symbol">))</a>
</pre>
### Constant sequences are arithmetic with common difference zero

<pre class="Agda"><a id="7377" class="Keyword">module</a> <a id="7384" href="ring-theory.arithmetic-sequences-semirings.html#7384" class="Module">_</a>
  <a id="7388" class="Symbol">{</a><a id="7389" href="ring-theory.arithmetic-sequences-semirings.html#7389" class="Bound">l</a> <a id="7391" class="Symbol">:</a> <a id="7393" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7398" class="Symbol">}</a> <a id="7400" class="Symbol">(</a><a id="7401" href="ring-theory.arithmetic-sequences-semirings.html#7401" class="Bound">R</a> <a id="7403" class="Symbol">:</a> <a id="7405" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="7414" href="ring-theory.arithmetic-sequences-semirings.html#7389" class="Bound">l</a><a id="7415" class="Symbol">)</a> <a id="7417" class="Symbol">(</a><a id="7418" href="ring-theory.arithmetic-sequences-semirings.html#7418" class="Bound">a</a> <a id="7420" class="Symbol">:</a> <a id="7422" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="7436" href="ring-theory.arithmetic-sequences-semirings.html#7401" class="Bound">R</a><a id="7437" class="Symbol">)</a>
  <a id="7441" class="Keyword">where</a>

  <a id="7450" href="ring-theory.arithmetic-sequences-semirings.html#7450" class="Function">zero-is-common-difference-const-sequence-Semiring</a> <a id="7500" class="Symbol">:</a>
    <a id="7506" href="group-theory.arithmetic-sequences-semigroups.html#1788" class="Function">is-common-difference-sequence-Semigroup</a>
      <a id="7552" class="Symbol">(</a> <a id="7554" href="ring-theory.semirings.html#2815" class="Function">additive-semigroup-Semiring</a> <a id="7582" href="ring-theory.arithmetic-sequences-semirings.html#7401" class="Bound">R</a><a id="7583" class="Symbol">)</a>
      <a id="7591" class="Symbol">(</a> <a id="7593" class="Symbol">λ</a> <a id="7595" href="ring-theory.arithmetic-sequences-semirings.html#7595" class="Symbol">_</a> <a id="7597" class="Symbol">→</a> <a id="7599" href="ring-theory.arithmetic-sequences-semirings.html#7418" class="Bound">a</a><a id="7600" class="Symbol">)</a>
      <a id="7608" class="Symbol">(</a> <a id="7610" href="ring-theory.semirings.html#5660" class="Function">zero-Semiring</a> <a id="7624" href="ring-theory.arithmetic-sequences-semirings.html#7401" class="Bound">R</a><a id="7625" class="Symbol">)</a>
  <a id="7629" href="ring-theory.arithmetic-sequences-semirings.html#7450" class="Function">zero-is-common-difference-const-sequence-Semiring</a> <a id="7679" href="ring-theory.arithmetic-sequences-semirings.html#7679" class="Bound">n</a> <a id="7681" class="Symbol">=</a>
    <a id="7687" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="7691" class="Symbol">(</a><a id="7692" href="ring-theory.semirings.html#6305" class="Function">right-unit-law-add-Semiring</a> <a id="7720" href="ring-theory.arithmetic-sequences-semirings.html#7401" class="Bound">R</a> <a id="7722" href="ring-theory.arithmetic-sequences-semirings.html#7418" class="Bound">a</a><a id="7723" class="Symbol">)</a>

  <a id="7728" href="ring-theory.arithmetic-sequences-semirings.html#7728" class="Function">arithmetic-const-sequence-Semiring</a> <a id="7763" class="Symbol">:</a> <a id="7765" href="ring-theory.arithmetic-sequences-semirings.html#1226" class="Function">arithmetic-sequence-Semiring</a> <a id="7794" href="ring-theory.arithmetic-sequences-semirings.html#7401" class="Bound">R</a>
  <a id="7798" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="7802" href="ring-theory.arithmetic-sequences-semirings.html#7728" class="Function">arithmetic-const-sequence-Semiring</a> <a id="7837" class="Symbol">_</a> <a id="7839" class="Symbol">=</a> <a id="7841" href="ring-theory.arithmetic-sequences-semirings.html#7418" class="Bound">a</a>
  <a id="7845" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="7849" href="ring-theory.arithmetic-sequences-semirings.html#7728" class="Function">arithmetic-const-sequence-Semiring</a> <a id="7884" class="Symbol">=</a>
    <a id="7890" class="Symbol">(</a> <a id="7892" href="ring-theory.semirings.html#5660" class="Function">zero-Semiring</a> <a id="7906" href="ring-theory.arithmetic-sequences-semirings.html#7401" class="Bound">R</a> <a id="7908" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="7910" href="ring-theory.arithmetic-sequences-semirings.html#7450" class="Function">zero-is-common-difference-const-sequence-Semiring</a><a id="7959" class="Symbol">)</a>
</pre>
## External links

- [Arithmetic progressions](https://en.wikipedia.org/wiki/Arithmetic_progression)
  at Wikipedia
