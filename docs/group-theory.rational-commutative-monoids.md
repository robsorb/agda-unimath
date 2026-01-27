# Rational commutative monoids

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="group-theory.rational-commutative-monoids.html" class="Module">group-theory.rational-commutative-monoids</a> <a id="90" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="146" class="Keyword">open</a> <a id="151" class="Keyword">import</a> <a id="158" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="280" class="Keyword">open</a> <a id="285" class="Keyword">import</a> <a id="292" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="318" class="Keyword">open</a> <a id="323" class="Keyword">import</a> <a id="330" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="354" class="Keyword">open</a> <a id="359" class="Keyword">import</a> <a id="366" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="394" class="Keyword">open</a> <a id="399" class="Keyword">import</a> <a id="406" href="group-theory.commutative-monoids.html" class="Module">group-theory.commutative-monoids</a>
<a id="439" class="Keyword">open</a> <a id="444" class="Keyword">import</a> <a id="451" href="group-theory.monoids.html" class="Module">group-theory.monoids</a>
<a id="472" class="Keyword">open</a> <a id="477" class="Keyword">import</a> <a id="484" href="group-theory.powers-of-elements-commutative-monoids.html" class="Module">group-theory.powers-of-elements-commutative-monoids</a>
</pre>
</details>

## Idea

A **rational commutative monoid** is a
[commutative monoid](group-theory.commutative-monoids.md) `(M,0,+)` in which the
map `x ↦ nx` is invertible for every
[natural number](elementary-number-theory.natural-numbers.md) `n > 0`. This
condition implies that we can invert the natural numbers in `M`, which are the
elements of the form `n1` in `M`.

Note: Since we usually write commutative monoids multiplicatively, the condition
that a commutative monoid is rational is that the map `x ↦ xⁿ` is invertible for
every natural number `n > 0`. However, for rational commutative monoids we will
write the binary operation additively.

## Definition

### The predicate of being a rational commutative monoid

<pre class="Agda"><a id="1272" class="Keyword">module</a> <a id="1279" href="group-theory.rational-commutative-monoids.html#1279" class="Module">_</a>
  <a id="1283" class="Symbol">{</a><a id="1284" href="group-theory.rational-commutative-monoids.html#1284" class="Bound">l</a> <a id="1286" class="Symbol">:</a> <a id="1288" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1293" class="Symbol">}</a> <a id="1295" class="Symbol">(</a><a id="1296" href="group-theory.rational-commutative-monoids.html#1296" class="Bound">M</a> <a id="1298" class="Symbol">:</a> <a id="1300" href="group-theory.commutative-monoids.html#1458" class="Function">Commutative-Monoid</a> <a id="1319" href="group-theory.rational-commutative-monoids.html#1284" class="Bound">l</a><a id="1320" class="Symbol">)</a>
  <a id="1324" class="Keyword">where</a>

  <a id="1333" href="group-theory.rational-commutative-monoids.html#1333" class="Function">is-rational-prop-Commutative-Monoid</a> <a id="1369" class="Symbol">:</a> <a id="1371" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1376" href="group-theory.rational-commutative-monoids.html#1284" class="Bound">l</a>
  <a id="1380" href="group-theory.rational-commutative-monoids.html#1333" class="Function">is-rational-prop-Commutative-Monoid</a> <a id="1416" class="Symbol">=</a>
    <a id="1422" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="1429" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
      <a id="1437" class="Symbol">(</a> <a id="1439" class="Symbol">λ</a> <a id="1441" href="group-theory.rational-commutative-monoids.html#1441" class="Bound">n</a> <a id="1443" class="Symbol">→</a>
        <a id="1453" href="foundation.equivalences.html#5072" class="Function">is-equiv-Prop</a> <a id="1467" class="Symbol">(</a><a id="1468" href="group-theory.powers-of-elements-commutative-monoids.html#967" class="Function">power-Commutative-Monoid</a> <a id="1493" href="group-theory.rational-commutative-monoids.html#1296" class="Bound">M</a> <a id="1495" class="Symbol">(</a><a id="1496" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1503" href="group-theory.rational-commutative-monoids.html#1441" class="Bound">n</a><a id="1504" class="Symbol">)))</a>

  <a id="1511" href="group-theory.rational-commutative-monoids.html#1511" class="Function">is-rational-Commutative-Monoid</a> <a id="1542" class="Symbol">:</a> <a id="1544" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1547" href="group-theory.rational-commutative-monoids.html#1284" class="Bound">l</a>
  <a id="1551" href="group-theory.rational-commutative-monoids.html#1511" class="Function">is-rational-Commutative-Monoid</a> <a id="1582" class="Symbol">=</a>
    <a id="1588" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1598" href="group-theory.rational-commutative-monoids.html#1333" class="Function">is-rational-prop-Commutative-Monoid</a>

  <a id="1637" href="group-theory.rational-commutative-monoids.html#1637" class="Function">is-prop-is-rational-Commutative-Monoid</a> <a id="1676" class="Symbol">:</a>
    <a id="1682" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1690" href="group-theory.rational-commutative-monoids.html#1511" class="Function">is-rational-Commutative-Monoid</a>
  <a id="1723" href="group-theory.rational-commutative-monoids.html#1637" class="Function">is-prop-is-rational-Commutative-Monoid</a> <a id="1762" class="Symbol">=</a>
    <a id="1768" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1786" href="group-theory.rational-commutative-monoids.html#1333" class="Function">is-rational-prop-Commutative-Monoid</a>
</pre>
### Rational commutative monoids

<pre class="Agda"><a id="Rational-Commutative-Monoid"></a><a id="1869" href="group-theory.rational-commutative-monoids.html#1869" class="Function">Rational-Commutative-Monoid</a> <a id="1897" class="Symbol">:</a> <a id="1899" class="Symbol">(</a><a id="1900" href="group-theory.rational-commutative-monoids.html#1900" class="Bound">l</a> <a id="1902" class="Symbol">:</a> <a id="1904" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1909" class="Symbol">)</a> <a id="1911" class="Symbol">→</a> <a id="1913" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1916" class="Symbol">(</a><a id="1917" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1922" href="group-theory.rational-commutative-monoids.html#1900" class="Bound">l</a><a id="1923" class="Symbol">)</a>
<a id="1925" href="group-theory.rational-commutative-monoids.html#1869" class="Function">Rational-Commutative-Monoid</a> <a id="1953" href="group-theory.rational-commutative-monoids.html#1953" class="Bound">l</a> <a id="1955" class="Symbol">=</a>
  <a id="1959" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1961" class="Symbol">(</a><a id="1962" href="group-theory.commutative-monoids.html#1458" class="Function">Commutative-Monoid</a> <a id="1981" href="group-theory.rational-commutative-monoids.html#1953" class="Bound">l</a><a id="1982" class="Symbol">)</a> <a id="1984" href="group-theory.rational-commutative-monoids.html#1511" class="Function">is-rational-Commutative-Monoid</a>

<a id="2016" class="Keyword">module</a> <a id="2023" href="group-theory.rational-commutative-monoids.html#2023" class="Module">_</a>
  <a id="2027" class="Symbol">{</a><a id="2028" href="group-theory.rational-commutative-monoids.html#2028" class="Bound">l</a> <a id="2030" class="Symbol">:</a> <a id="2032" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2037" class="Symbol">}</a> <a id="2039" class="Symbol">(</a><a id="2040" href="group-theory.rational-commutative-monoids.html#2040" class="Bound">M</a> <a id="2042" class="Symbol">:</a> <a id="2044" href="group-theory.rational-commutative-monoids.html#1869" class="Function">Rational-Commutative-Monoid</a> <a id="2072" href="group-theory.rational-commutative-monoids.html#2028" class="Bound">l</a><a id="2073" class="Symbol">)</a>
  <a id="2077" class="Keyword">where</a>

  <a id="2086" href="group-theory.rational-commutative-monoids.html#2086" class="Function">commutative-monoid-Rational-Commutative-Monoid</a> <a id="2133" class="Symbol">:</a> <a id="2135" href="group-theory.commutative-monoids.html#1458" class="Function">Commutative-Monoid</a> <a id="2154" href="group-theory.rational-commutative-monoids.html#2028" class="Bound">l</a>
  <a id="2158" href="group-theory.rational-commutative-monoids.html#2086" class="Function">commutative-monoid-Rational-Commutative-Monoid</a> <a id="2205" class="Symbol">=</a> <a id="2207" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2211" href="group-theory.rational-commutative-monoids.html#2040" class="Bound">M</a>

  <a id="2216" href="group-theory.rational-commutative-monoids.html#2216" class="Function">monoid-Rational-Commutative-Monoid</a> <a id="2251" class="Symbol">:</a> <a id="2253" href="group-theory.monoids.html#835" class="Function">Monoid</a> <a id="2260" href="group-theory.rational-commutative-monoids.html#2028" class="Bound">l</a>
  <a id="2264" href="group-theory.rational-commutative-monoids.html#2216" class="Function">monoid-Rational-Commutative-Monoid</a> <a id="2299" class="Symbol">=</a>
    <a id="2305" href="group-theory.commutative-monoids.html#1625" class="Function">monoid-Commutative-Monoid</a> <a id="2331" href="group-theory.rational-commutative-monoids.html#2086" class="Function">commutative-monoid-Rational-Commutative-Monoid</a>

  <a id="2381" href="group-theory.rational-commutative-monoids.html#2381" class="Function">type-Rational-Commutative-Monoid</a> <a id="2414" class="Symbol">:</a> <a id="2416" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2419" href="group-theory.rational-commutative-monoids.html#2028" class="Bound">l</a>
  <a id="2423" href="group-theory.rational-commutative-monoids.html#2381" class="Function">type-Rational-Commutative-Monoid</a> <a id="2456" class="Symbol">=</a>
    <a id="2462" href="group-theory.commutative-monoids.html#2080" class="Function">type-Commutative-Monoid</a> <a id="2486" href="group-theory.rational-commutative-monoids.html#2086" class="Function">commutative-monoid-Rational-Commutative-Monoid</a>

  <a id="2536" href="group-theory.rational-commutative-monoids.html#2536" class="Function">add-Rational-Commutative-Monoid</a> <a id="2568" class="Symbol">:</a>
    <a id="2574" class="Symbol">(</a><a id="2575" href="group-theory.rational-commutative-monoids.html#2575" class="Bound">x</a> <a id="2577" href="group-theory.rational-commutative-monoids.html#2577" class="Bound">y</a> <a id="2579" class="Symbol">:</a> <a id="2581" href="group-theory.rational-commutative-monoids.html#2381" class="Function">type-Rational-Commutative-Monoid</a><a id="2613" class="Symbol">)</a> <a id="2615" class="Symbol">→</a>
    <a id="2621" href="group-theory.rational-commutative-monoids.html#2381" class="Function">type-Rational-Commutative-Monoid</a>
  <a id="2656" href="group-theory.rational-commutative-monoids.html#2536" class="Function">add-Rational-Commutative-Monoid</a> <a id="2688" class="Symbol">=</a>
    <a id="2694" href="group-theory.commutative-monoids.html#2598" class="Function">mul-Commutative-Monoid</a> <a id="2717" href="group-theory.rational-commutative-monoids.html#2086" class="Function">commutative-monoid-Rational-Commutative-Monoid</a>

  <a id="2767" href="group-theory.rational-commutative-monoids.html#2767" class="Function">zero-Rational-Commutative-Monoid</a> <a id="2800" class="Symbol">:</a> <a id="2802" href="group-theory.rational-commutative-monoids.html#2381" class="Function">type-Rational-Commutative-Monoid</a>
  <a id="2837" href="group-theory.rational-commutative-monoids.html#2767" class="Function">zero-Rational-Commutative-Monoid</a> <a id="2870" class="Symbol">=</a>
    <a id="2876" href="group-theory.commutative-monoids.html#4971" class="Function">unit-Commutative-Monoid</a> <a id="2900" href="group-theory.rational-commutative-monoids.html#2086" class="Function">commutative-monoid-Rational-Commutative-Monoid</a>

  <a id="2950" href="group-theory.rational-commutative-monoids.html#2950" class="Function">associative-add-Rational-Commutative-Monoid</a> <a id="2994" class="Symbol">:</a>
    <a id="3000" class="Symbol">(</a><a id="3001" href="group-theory.rational-commutative-monoids.html#3001" class="Bound">x</a> <a id="3003" href="group-theory.rational-commutative-monoids.html#3003" class="Bound">y</a> <a id="3005" href="group-theory.rational-commutative-monoids.html#3005" class="Bound">z</a> <a id="3007" class="Symbol">:</a> <a id="3009" href="group-theory.rational-commutative-monoids.html#2381" class="Function">type-Rational-Commutative-Monoid</a><a id="3041" class="Symbol">)</a> <a id="3043" class="Symbol">→</a>
    <a id="3049" href="group-theory.rational-commutative-monoids.html#2536" class="Function">add-Rational-Commutative-Monoid</a>
      <a id="3087" class="Symbol">(</a> <a id="3089" href="group-theory.rational-commutative-monoids.html#2536" class="Function">add-Rational-Commutative-Monoid</a> <a id="3121" href="group-theory.rational-commutative-monoids.html#3001" class="Bound">x</a> <a id="3123" href="group-theory.rational-commutative-monoids.html#3003" class="Bound">y</a><a id="3124" class="Symbol">)</a>
      <a id="3132" class="Symbol">(</a> <a id="3134" href="group-theory.rational-commutative-monoids.html#3005" class="Bound">z</a><a id="3135" class="Symbol">)</a> <a id="3137" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="3143" href="group-theory.rational-commutative-monoids.html#2536" class="Function">add-Rational-Commutative-Monoid</a>
      <a id="3181" class="Symbol">(</a> <a id="3183" href="group-theory.rational-commutative-monoids.html#3001" class="Bound">x</a><a id="3184" class="Symbol">)</a>
      <a id="3192" class="Symbol">(</a> <a id="3194" href="group-theory.rational-commutative-monoids.html#2536" class="Function">add-Rational-Commutative-Monoid</a> <a id="3226" href="group-theory.rational-commutative-monoids.html#3003" class="Bound">y</a> <a id="3228" href="group-theory.rational-commutative-monoids.html#3005" class="Bound">z</a><a id="3229" class="Symbol">)</a>
  <a id="3233" href="group-theory.rational-commutative-monoids.html#2950" class="Function">associative-add-Rational-Commutative-Monoid</a> <a id="3277" class="Symbol">=</a>
    <a id="3283" href="group-theory.commutative-monoids.html#3146" class="Function">associative-mul-Commutative-Monoid</a>
      <a id="3324" href="group-theory.rational-commutative-monoids.html#2086" class="Function">commutative-monoid-Rational-Commutative-Monoid</a>

  <a id="3374" href="group-theory.rational-commutative-monoids.html#3374" class="Function">left-unit-law-add-Rational-Commutative-Monoid</a> <a id="3420" class="Symbol">:</a>
    <a id="3426" class="Symbol">(</a><a id="3427" href="group-theory.rational-commutative-monoids.html#3427" class="Bound">x</a> <a id="3429" class="Symbol">:</a> <a id="3431" href="group-theory.rational-commutative-monoids.html#2381" class="Function">type-Rational-Commutative-Monoid</a><a id="3463" class="Symbol">)</a> <a id="3465" class="Symbol">→</a>
    <a id="3471" href="group-theory.rational-commutative-monoids.html#2536" class="Function">add-Rational-Commutative-Monoid</a> <a id="3503" href="group-theory.rational-commutative-monoids.html#2767" class="Function">zero-Rational-Commutative-Monoid</a> <a id="3536" href="group-theory.rational-commutative-monoids.html#3427" class="Bound">x</a> <a id="3538" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="3540" href="group-theory.rational-commutative-monoids.html#3427" class="Bound">x</a>
  <a id="3544" href="group-theory.rational-commutative-monoids.html#3374" class="Function">left-unit-law-add-Rational-Commutative-Monoid</a> <a id="3590" class="Symbol">=</a>
    <a id="3596" href="group-theory.commutative-monoids.html#5096" class="Function">left-unit-law-mul-Commutative-Monoid</a>
      <a id="3639" href="group-theory.rational-commutative-monoids.html#2086" class="Function">commutative-monoid-Rational-Commutative-Monoid</a>

  <a id="3689" href="group-theory.rational-commutative-monoids.html#3689" class="Function">right-unit-law-add-Rational-Commutative-Monoid</a> <a id="3736" class="Symbol">:</a>
    <a id="3742" class="Symbol">(</a><a id="3743" href="group-theory.rational-commutative-monoids.html#3743" class="Bound">x</a> <a id="3745" class="Symbol">:</a> <a id="3747" href="group-theory.rational-commutative-monoids.html#2381" class="Function">type-Rational-Commutative-Monoid</a><a id="3779" class="Symbol">)</a> <a id="3781" class="Symbol">→</a>
    <a id="3787" href="group-theory.rational-commutative-monoids.html#2536" class="Function">add-Rational-Commutative-Monoid</a> <a id="3819" href="group-theory.rational-commutative-monoids.html#3743" class="Bound">x</a> <a id="3821" href="group-theory.rational-commutative-monoids.html#2767" class="Function">zero-Rational-Commutative-Monoid</a> <a id="3854" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="3856" href="group-theory.rational-commutative-monoids.html#3743" class="Bound">x</a>
  <a id="3860" href="group-theory.rational-commutative-monoids.html#3689" class="Function">right-unit-law-add-Rational-Commutative-Monoid</a> <a id="3907" class="Symbol">=</a>
    <a id="3913" href="group-theory.commutative-monoids.html#5335" class="Function">right-unit-law-mul-Commutative-Monoid</a>
      <a id="3957" href="group-theory.rational-commutative-monoids.html#2086" class="Function">commutative-monoid-Rational-Commutative-Monoid</a>

  <a id="4007" href="group-theory.rational-commutative-monoids.html#4007" class="Function">multiple-Rational-Commutative-Monoid</a> <a id="4044" class="Symbol">:</a>
    <a id="4050" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="4052" class="Symbol">→</a> <a id="4054" href="group-theory.rational-commutative-monoids.html#2381" class="Function">type-Rational-Commutative-Monoid</a> <a id="4087" class="Symbol">→</a> <a id="4089" href="group-theory.rational-commutative-monoids.html#2381" class="Function">type-Rational-Commutative-Monoid</a>
  <a id="4124" href="group-theory.rational-commutative-monoids.html#4007" class="Function">multiple-Rational-Commutative-Monoid</a> <a id="4161" class="Symbol">=</a>
    <a id="4167" href="group-theory.powers-of-elements-commutative-monoids.html#967" class="Function">power-Commutative-Monoid</a> <a id="4192" href="group-theory.rational-commutative-monoids.html#2086" class="Function">commutative-monoid-Rational-Commutative-Monoid</a>

  <a id="4242" href="group-theory.rational-commutative-monoids.html#4242" class="Function">is-rational-Rational-Commutative-Monoid</a> <a id="4282" class="Symbol">:</a>
    <a id="4288" href="group-theory.rational-commutative-monoids.html#1511" class="Function">is-rational-Commutative-Monoid</a>
      <a id="4325" href="group-theory.rational-commutative-monoids.html#2086" class="Function">commutative-monoid-Rational-Commutative-Monoid</a>
  <a id="4374" href="group-theory.rational-commutative-monoids.html#4242" class="Function">is-rational-Rational-Commutative-Monoid</a> <a id="4414" class="Symbol">=</a> <a id="4416" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4420" href="group-theory.rational-commutative-monoids.html#2040" class="Bound">M</a>
</pre>