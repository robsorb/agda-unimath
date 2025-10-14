# The minimum of inhabited, finitely enumerable subsets of real numbers

<pre class="Agda"><a id="82" class="Symbol">{-#</a> <a id="86" class="Keyword">OPTIONS</a> <a id="94" class="Pragma">--lossy-unification</a> <a id="114" class="Symbol">#-}</a>

<a id="119" class="Keyword">module</a> <a id="126" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html" class="Module">real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers</a> <a id="198" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="298" class="Keyword">open</a> <a id="303" class="Keyword">import</a> <a id="310" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="order-theory.greatest-lower-bounds-large-posets.html" class="Module">order-theory.greatest-lower-bounds-large-posets</a>
<a id="398" class="Keyword">open</a> <a id="403" class="Keyword">import</a> <a id="410" href="order-theory.lower-bounds-large-posets.html" class="Module">order-theory.lower-bounds-large-posets</a>

<a id="450" class="Keyword">open</a> <a id="455" class="Keyword">import</a> <a id="462" href="real-numbers.dedekind-real-numbers.html" class="Module">real-numbers.dedekind-real-numbers</a>
<a id="497" class="Keyword">open</a> <a id="502" class="Keyword">import</a> <a id="509" href="real-numbers.inequality-real-numbers.html" class="Module">real-numbers.inequality-real-numbers</a>
<a id="546" class="Keyword">open</a> <a id="551" class="Keyword">import</a> <a id="558" href="real-numbers.infima-families-real-numbers.html" class="Module">real-numbers.infima-families-real-numbers</a>
<a id="600" class="Keyword">open</a> <a id="605" class="Keyword">import</a> <a id="612" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html" class="Module">real-numbers.inhabited-finitely-enumerable-subsets-real-numbers</a>
<a id="676" class="Keyword">open</a> <a id="681" class="Keyword">import</a> <a id="688" href="real-numbers.maximum-inhabited-finitely-enumerable-subsets-real-numbers.html" class="Module">real-numbers.maximum-inhabited-finitely-enumerable-subsets-real-numbers</a>
<a id="760" class="Keyword">open</a> <a id="765" class="Keyword">import</a> <a id="772" href="real-numbers.negation-real-numbers.html" class="Module">real-numbers.negation-real-numbers</a>
<a id="807" class="Keyword">open</a> <a id="812" class="Keyword">import</a> <a id="819" href="real-numbers.subsets-real-numbers.html" class="Module">real-numbers.subsets-real-numbers</a>

<a id="854" class="Keyword">open</a> <a id="859" class="Keyword">import</a> <a id="866" href="univalent-combinatorics.finitely-enumerable-subtypes.html" class="Module">univalent-combinatorics.finitely-enumerable-subtypes</a>
</pre>
</details>

## Idea

The
{{#concept "minimum" Disambiguation="inhabited finitely enumerable subset of Dedekind real numbers" Agda=min-inhabited-finitely-enumerable-subset-ℝ WD="minimum" WDID=Q10585806}}
of an
[inhabited, finitely enumerable subset of the real numbers](real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.md)
is their [infimum](real-numbers.infima-families-real-numbers.md).

## Definition

<pre class="Agda"><a id="1351" class="Keyword">module</a> <a id="1358" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1358" class="Module">_</a>
  <a id="1362" class="Symbol">{</a><a id="1363" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1363" class="Bound">l1</a> <a id="1366" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1366" class="Bound">l2</a> <a id="1369" class="Symbol">:</a> <a id="1371" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1376" class="Symbol">}</a> <a id="1378" class="Symbol">(</a><a id="1379" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1379" class="Bound">S</a> <a id="1381" class="Symbol">:</a> <a id="1383" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1200" class="Function">inhabited-finitely-enumerable-subset-ℝ</a> <a id="1422" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1363" class="Bound">l1</a> <a id="1425" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1366" class="Bound">l2</a><a id="1427" class="Symbol">)</a>
  <a id="1431" class="Keyword">where</a>

  <a id="1440" class="Keyword">opaque</a>
    <a id="1451" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1451" class="Function">min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="1494" class="Symbol">:</a> <a id="1496" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="1498" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1366" class="Bound">l2</a>
    <a id="1505" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1451" class="Function">min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="1548" class="Symbol">=</a>
      <a id="1556" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a>
        <a id="1570" class="Symbol">(</a> <a id="1572" href="real-numbers.maximum-inhabited-finitely-enumerable-subsets-real-numbers.html#6641" class="Function">max-inhabited-finitely-enumerable-subset-ℝ</a>
          <a id="1625" class="Symbol">(</a> <a id="1627" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2669" class="Function">neg-inhabited-finitely-enumerable-subset-ℝ</a> <a id="1670" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1379" class="Bound">S</a><a id="1671" class="Symbol">))</a>
</pre>
## Properties

### The minimum is the infimum

<pre class="Agda"><a id="1734" class="Keyword">module</a> <a id="1741" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1741" class="Module">_</a>
  <a id="1745" class="Symbol">{</a><a id="1746" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1746" class="Bound">l1</a> <a id="1749" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1749" class="Bound">l2</a> <a id="1752" class="Symbol">:</a> <a id="1754" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1759" class="Symbol">}</a> <a id="1761" class="Symbol">(</a><a id="1762" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1762" class="Bound">S</a> <a id="1764" class="Symbol">:</a> <a id="1766" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1200" class="Function">inhabited-finitely-enumerable-subset-ℝ</a> <a id="1805" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1746" class="Bound">l1</a> <a id="1808" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1749" class="Bound">l2</a><a id="1810" class="Symbol">)</a>
  <a id="1814" class="Keyword">where</a>

  <a id="1823" class="Keyword">opaque</a>
    <a id="1834" class="Keyword">unfolding</a> <a id="1844" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1451" class="Function">min-inhabited-finitely-enumerable-subset-ℝ</a>

    <a id="1892" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1892" class="Function">is-infimum-min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="1946" class="Symbol">:</a>
      <a id="1954" href="real-numbers.infima-families-real-numbers.html#3888" class="Function">is-infimum-subset-ℝ</a>
        <a id="1982" class="Symbol">(</a> <a id="1984" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1471" class="Function">subset-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2030" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1762" class="Bound">S</a><a id="2031" class="Symbol">)</a>
        <a id="2041" class="Symbol">(</a> <a id="2043" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1451" class="Function">min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2086" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1762" class="Bound">S</a><a id="2087" class="Symbol">)</a>
    <a id="2093" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1892" class="Function">is-infimum-min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2147" class="Symbol">=</a>
      <a id="2155" href="real-numbers.infima-families-real-numbers.html#12615" class="Function">is-infimum-neg-supremum-neg-subset-ℝ</a>
        <a id="2200" class="Symbol">(</a> <a id="2202" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1471" class="Function">subset-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2248" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1762" class="Bound">S</a><a id="2249" class="Symbol">)</a>
        <a id="2259" class="Symbol">(</a> <a id="2261" href="real-numbers.maximum-inhabited-finitely-enumerable-subsets-real-numbers.html#6641" class="Function">max-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2304" class="Symbol">_)</a>
        <a id="2315" class="Symbol">(</a> <a id="2317" href="real-numbers.maximum-inhabited-finitely-enumerable-subsets-real-numbers.html#7021" class="Function">is-supremum-max-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2372" class="Symbol">_)</a>
</pre>
### Finitely enumerable subsets of the real numbers have an infimum

<pre class="Agda"><a id="2457" class="Keyword">module</a> <a id="2464" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2464" class="Module">_</a>
  <a id="2468" class="Symbol">{</a><a id="2469" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2469" class="Bound">l1</a> <a id="2472" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2472" class="Bound">l2</a> <a id="2475" class="Symbol">:</a> <a id="2477" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2482" class="Symbol">}</a> <a id="2484" class="Symbol">(</a><a id="2485" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2485" class="Bound">S</a> <a id="2487" class="Symbol">:</a> <a id="2489" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1200" class="Function">inhabited-finitely-enumerable-subset-ℝ</a> <a id="2528" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2469" class="Bound">l1</a> <a id="2531" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2472" class="Bound">l2</a><a id="2533" class="Symbol">)</a>
  <a id="2537" class="Keyword">where</a>

  <a id="2546" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2546" class="Function">has-infimum-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2597" class="Symbol">:</a>
    <a id="2603" href="real-numbers.infima-families-real-numbers.html#6759" class="Function">has-infimum-subset-ℝ</a> <a id="2624" class="Symbol">(</a><a id="2625" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1471" class="Function">subset-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2671" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2485" class="Bound">S</a><a id="2672" class="Symbol">)</a> <a id="2674" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2472" class="Bound">l2</a>
  <a id="2679" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2546" class="Function">has-infimum-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2730" class="Symbol">=</a>
    <a id="2736" class="Symbol">(</a> <a id="2738" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1451" class="Function">min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2781" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2485" class="Bound">S</a> <a id="2783" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="2791" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1892" class="Function">is-infimum-min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="2845" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2485" class="Bound">S</a><a id="2846" class="Symbol">)</a>
</pre>
### The minimum is the greatest lower bound

<pre class="Agda"><a id="2906" class="Keyword">module</a> <a id="2913" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2913" class="Module">_</a>
  <a id="2917" class="Symbol">{</a><a id="2918" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2918" class="Bound">l1</a> <a id="2921" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2921" class="Bound">l2</a> <a id="2924" class="Symbol">:</a> <a id="2926" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2931" class="Symbol">}</a> <a id="2933" class="Symbol">(</a><a id="2934" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2934" class="Bound">S</a> <a id="2936" class="Symbol">:</a> <a id="2938" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1200" class="Function">inhabited-finitely-enumerable-subset-ℝ</a> <a id="2977" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2918" class="Bound">l1</a> <a id="2980" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2921" class="Bound">l2</a><a id="2982" class="Symbol">)</a>
  <a id="2986" class="Keyword">where</a>

  <a id="2995" class="Keyword">abstract</a>
    <a id="3008" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3008" class="Function">is-greatest-lower-bound-min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="3075" class="Symbol">:</a>
      <a id="3083" href="order-theory.greatest-lower-bounds-large-posets.html#1568" class="Function">is-greatest-lower-bound-family-of-elements-Large-Poset</a>
        <a id="3146" class="Symbol">(</a> <a id="3148" href="real-numbers.inequality-real-numbers.html#5939" class="Function">ℝ-Large-Poset</a><a id="3161" class="Symbol">)</a>
        <a id="3171" class="Symbol">(</a> <a id="3173" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2089" class="Function">inclusion-inhabited-finitely-enumerable-subset-ℝ</a> <a id="3222" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2934" class="Bound">S</a><a id="3223" class="Symbol">)</a>
        <a id="3233" class="Symbol">(</a> <a id="3235" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1451" class="Function">min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="3278" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2934" class="Bound">S</a><a id="3279" class="Symbol">)</a>
    <a id="3285" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3008" class="Function">is-greatest-lower-bound-min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="3352" class="Symbol">=</a>
      <a id="3360" href="real-numbers.infima-families-real-numbers.html#4228" class="Function">is-greatest-lower-bound-is-infimum-family-ℝ</a>
        <a id="3412" class="Symbol">(</a> <a id="3414" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2089" class="Function">inclusion-inhabited-finitely-enumerable-subset-ℝ</a> <a id="3463" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2934" class="Bound">S</a><a id="3464" class="Symbol">)</a>
        <a id="3474" class="Symbol">(</a> <a id="3476" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1451" class="Function">min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="3519" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2934" class="Bound">S</a><a id="3520" class="Symbol">)</a>
        <a id="3530" class="Symbol">(</a> <a id="3532" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1892" class="Function">is-infimum-min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="3586" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#2934" class="Bound">S</a><a id="3587" class="Symbol">)</a>
</pre>
### The minimum is a lower bound

<pre class="Agda"><a id="3636" class="Keyword">module</a> <a id="3643" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3643" class="Module">_</a>
  <a id="3647" class="Symbol">{</a><a id="3648" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3648" class="Bound">l1</a> <a id="3651" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3651" class="Bound">l2</a> <a id="3654" class="Symbol">:</a> <a id="3656" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3661" class="Symbol">}</a> <a id="3663" class="Symbol">(</a><a id="3664" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3664" class="Bound">S</a> <a id="3666" class="Symbol">:</a> <a id="3668" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1200" class="Function">inhabited-finitely-enumerable-subset-ℝ</a> <a id="3707" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3648" class="Bound">l1</a> <a id="3710" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3651" class="Bound">l2</a><a id="3712" class="Symbol">)</a>
  <a id="3716" class="Keyword">where</a>

  <a id="3725" class="Keyword">abstract</a>
    <a id="3738" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3738" class="Function">is-lower-bound-min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="3796" class="Symbol">:</a>
      <a id="3804" href="order-theory.lower-bounds-large-posets.html#1951" class="Function">is-lower-bound-family-of-elements-Large-Poset</a>
        <a id="3858" class="Symbol">(</a> <a id="3860" href="real-numbers.inequality-real-numbers.html#5939" class="Function">ℝ-Large-Poset</a><a id="3873" class="Symbol">)</a>
        <a id="3883" class="Symbol">(</a> <a id="3885" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2089" class="Function">inclusion-inhabited-finitely-enumerable-subset-ℝ</a> <a id="3934" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3664" class="Bound">S</a><a id="3935" class="Symbol">)</a>
        <a id="3945" class="Symbol">(</a> <a id="3947" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1451" class="Function">min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="3990" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3664" class="Bound">S</a><a id="3991" class="Symbol">)</a>
    <a id="3997" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3738" class="Function">is-lower-bound-min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="4055" class="Symbol">=</a>
      <a id="4063" href="real-numbers.infima-families-real-numbers.html#3219" class="Function">is-lower-bound-is-infimum-family-ℝ</a>
        <a id="4106" class="Symbol">(</a> <a id="4108" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2089" class="Function">inclusion-inhabited-finitely-enumerable-subset-ℝ</a> <a id="4157" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3664" class="Bound">S</a><a id="4158" class="Symbol">)</a>
        <a id="4168" class="Symbol">(</a> <a id="4170" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1451" class="Function">min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="4213" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3664" class="Bound">S</a><a id="4214" class="Symbol">)</a>
        <a id="4224" class="Symbol">(</a> <a id="4226" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1892" class="Function">is-infimum-min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="4280" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#3664" class="Bound">S</a><a id="4281" class="Symbol">)</a>
</pre>
### The minimum is approximated above

<pre class="Agda"><a id="4335" class="Keyword">module</a> <a id="4342" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#4342" class="Module">_</a>
  <a id="4346" class="Symbol">{</a><a id="4347" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#4347" class="Bound">l1</a> <a id="4350" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#4350" class="Bound">l2</a> <a id="4353" class="Symbol">:</a> <a id="4355" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4360" class="Symbol">}</a> <a id="4362" class="Symbol">(</a><a id="4363" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#4363" class="Bound">S</a> <a id="4365" class="Symbol">:</a> <a id="4367" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#1200" class="Function">inhabited-finitely-enumerable-subset-ℝ</a> <a id="4406" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#4347" class="Bound">l1</a> <a id="4409" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#4350" class="Bound">l2</a><a id="4411" class="Symbol">)</a>
  <a id="4415" class="Keyword">where</a>

  <a id="4424" class="Keyword">abstract</a>
    <a id="4437" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#4437" class="Function">is-approximated-above-min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="4502" class="Symbol">:</a>
      <a id="4510" href="real-numbers.infima-families-real-numbers.html#2675" class="Function">is-approximated-above-family-ℝ</a>
        <a id="4549" class="Symbol">(</a> <a id="4551" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2089" class="Function">inclusion-inhabited-finitely-enumerable-subset-ℝ</a> <a id="4600" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#4363" class="Bound">S</a><a id="4601" class="Symbol">)</a>
        <a id="4611" class="Symbol">(</a> <a id="4613" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1451" class="Function">min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="4656" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#4363" class="Bound">S</a><a id="4657" class="Symbol">)</a>
    <a id="4663" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#4437" class="Function">is-approximated-above-min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="4728" class="Symbol">=</a>
      <a id="4736" href="real-numbers.infima-families-real-numbers.html#3428" class="Function">is-approximated-above-is-infimum-family-ℝ</a>
        <a id="4786" class="Symbol">(</a> <a id="4788" href="real-numbers.inhabited-finitely-enumerable-subsets-real-numbers.html#2089" class="Function">inclusion-inhabited-finitely-enumerable-subset-ℝ</a> <a id="4837" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#4363" class="Bound">S</a><a id="4838" class="Symbol">)</a>
        <a id="4848" class="Symbol">(</a> <a id="4850" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1451" class="Function">min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="4893" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#4363" class="Bound">S</a><a id="4894" class="Symbol">)</a>
        <a id="4904" class="Symbol">(</a> <a id="4906" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#1892" class="Function">is-infimum-min-inhabited-finitely-enumerable-subset-ℝ</a> <a id="4960" href="real-numbers.minimum-inhabited-finitely-enumerable-subsets-real-numbers.html#4363" class="Bound">S</a><a id="4961" class="Symbol">)</a>
</pre>