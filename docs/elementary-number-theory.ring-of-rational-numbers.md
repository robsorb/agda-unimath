# The ring of rational numbers

<pre class="Agda"><a id="41" class="Symbol">{-#</a> <a id="45" class="Keyword">OPTIONS</a> <a id="53" class="Pragma">--lossy-unification</a> <a id="73" class="Symbol">#-}</a>

<a id="78" class="Keyword">module</a> <a id="85" href="elementary-number-theory.ring-of-rational-numbers.html" class="Module">elementary-number-theory.ring-of-rational-numbers</a> <a id="135" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="191" class="Keyword">open</a> <a id="196" class="Keyword">import</a> <a id="203" href="commutative-algebra.commutative-rings.html" class="Module">commutative-algebra.commutative-rings</a>

<a id="242" class="Keyword">open</a> <a id="247" class="Keyword">import</a> <a id="254" href="elementary-number-theory.additive-group-of-rational-numbers.html" class="Module">elementary-number-theory.additive-group-of-rational-numbers</a>
<a id="314" class="Keyword">open</a> <a id="319" class="Keyword">import</a> <a id="326" href="elementary-number-theory.multiplication-rational-numbers.html" class="Module">elementary-number-theory.multiplication-rational-numbers</a>
<a id="383" class="Keyword">open</a> <a id="388" class="Keyword">import</a> <a id="395" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html" class="Module">elementary-number-theory.multiplicative-monoid-of-rational-numbers</a>
<a id="462" class="Keyword">open</a> <a id="467" class="Keyword">import</a> <a id="474" href="elementary-number-theory.positive-integers.html" class="Module">elementary-number-theory.positive-integers</a>
<a id="517" class="Keyword">open</a> <a id="522" class="Keyword">import</a> <a id="529" href="elementary-number-theory.rational-numbers.html" class="Module">elementary-number-theory.rational-numbers</a>
<a id="571" class="Keyword">open</a> <a id="576" class="Keyword">import</a> <a id="583" href="elementary-number-theory.ring-of-integers.html" class="Module">elementary-number-theory.ring-of-integers</a>
<a id="625" class="Keyword">open</a> <a id="630" class="Keyword">import</a> <a id="637" href="elementary-number-theory.unit-fractions-rational-numbers.html" class="Module">elementary-number-theory.unit-fractions-rational-numbers</a>

<a id="695" class="Keyword">open</a> <a id="700" class="Keyword">import</a> <a id="707" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="734" class="Keyword">open</a> <a id="739" class="Keyword">import</a> <a id="746" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="778" class="Keyword">open</a> <a id="783" class="Keyword">import</a> <a id="790" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="812" class="Keyword">open</a> <a id="817" class="Keyword">import</a> <a id="824" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="850" class="Keyword">open</a> <a id="855" class="Keyword">import</a> <a id="862" href="foundation.unital-binary-operations.html" class="Module">foundation.unital-binary-operations</a>
<a id="898" class="Keyword">open</a> <a id="903" class="Keyword">import</a> <a id="910" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="938" class="Keyword">open</a> <a id="943" class="Keyword">import</a> <a id="950" href="group-theory.semigroups.html" class="Module">group-theory.semigroups</a>

<a id="975" class="Keyword">open</a> <a id="980" class="Keyword">import</a> <a id="987" href="ring-theory.homomorphisms-rings.html" class="Module">ring-theory.homomorphisms-rings</a>
<a id="1019" class="Keyword">open</a> <a id="1024" class="Keyword">import</a> <a id="1031" href="ring-theory.localizations-rings.html" class="Module">ring-theory.localizations-rings</a>
<a id="1063" class="Keyword">open</a> <a id="1068" class="Keyword">import</a> <a id="1075" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
</details>

## Idea

The
[additive group of rational numbers](elementary-number-theory.additive-group-of-rational-numbers.md)
equipped with
[multiplication](elementary-number-theory.multiplication-rational-numbers.md) is
a commutative [division ring](ring-theory.division-rings.md).

## Definitions

### The compatible multiplicative structure on the abelian group of rational numbers

<pre class="Agda"><a id="has-mul-abelian-group-add-ℚ"></a><a id="1492" href="elementary-number-theory.ring-of-rational-numbers.html#1492" class="Function">has-mul-abelian-group-add-ℚ</a> <a id="1520" class="Symbol">:</a> <a id="1522" href="ring-theory.rings.html#1607" class="Function">has-mul-Ab</a> <a id="1533" href="elementary-number-theory.additive-group-of-rational-numbers.html#2116" class="Function">abelian-group-add-ℚ</a>
<a id="1553" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1557" href="elementary-number-theory.ring-of-rational-numbers.html#1492" class="Function">has-mul-abelian-group-add-ℚ</a> <a id="1585" class="Symbol">=</a> <a id="1587" href="group-theory.semigroups.html#1240" class="Function">has-associative-mul-Semigroup</a> <a id="1617" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#942" class="Function">semigroup-mul-ℚ</a>
<a id="1633" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1637" class="Symbol">(</a><a id="1638" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1642" href="elementary-number-theory.ring-of-rational-numbers.html#1492" class="Function">has-mul-abelian-group-add-ℚ</a><a id="1669" class="Symbol">)</a> <a id="1671" class="Symbol">=</a> <a id="1673" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#1085" class="Function">is-unital-mul-ℚ</a>
<a id="1689" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1693" class="Symbol">(</a><a id="1694" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1698" class="Symbol">(</a><a id="1699" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1703" href="elementary-number-theory.ring-of-rational-numbers.html#1492" class="Function">has-mul-abelian-group-add-ℚ</a><a id="1730" class="Symbol">))</a> <a id="1733" class="Symbol">=</a> <a id="1735" href="elementary-number-theory.multiplication-rational-numbers.html#8748" class="Function">left-distributive-mul-add-ℚ</a>
<a id="1763" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1767" class="Symbol">(</a><a id="1768" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1772" class="Symbol">(</a><a id="1773" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1777" href="elementary-number-theory.ring-of-rational-numbers.html#1492" class="Function">has-mul-abelian-group-add-ℚ</a><a id="1804" class="Symbol">))</a> <a id="1807" class="Symbol">=</a> <a id="1809" href="elementary-number-theory.multiplication-rational-numbers.html#10715" class="Function">right-distributive-mul-add-ℚ</a>
</pre>
### The ring of rational numbers

<pre class="Agda"><a id="ring-ℚ"></a><a id="1885" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a> <a id="1892" class="Symbol">:</a> <a id="1894" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="1899" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1905" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1909" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a> <a id="1916" class="Symbol">=</a> <a id="1918" href="elementary-number-theory.additive-group-of-rational-numbers.html#2116" class="Function">abelian-group-add-ℚ</a>
<a id="1938" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1942" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a> <a id="1949" class="Symbol">=</a> <a id="1951" href="elementary-number-theory.ring-of-rational-numbers.html#1492" class="Function">has-mul-abelian-group-add-ℚ</a>
</pre>
## Properties

### The ring of rational numbers is commutative

<pre class="Agda"><a id="commutative-ring-ℚ"></a><a id="2056" href="elementary-number-theory.ring-of-rational-numbers.html#2056" class="Function">commutative-ring-ℚ</a> <a id="2075" class="Symbol">:</a> <a id="2077" href="commutative-algebra.commutative-rings.html#2100" class="Function">Commutative-Ring</a> <a id="2094" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2100" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2104" href="elementary-number-theory.ring-of-rational-numbers.html#2056" class="Function">commutative-ring-ℚ</a> <a id="2123" class="Symbol">=</a> <a id="2125" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a>
<a id="2132" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2136" href="elementary-number-theory.ring-of-rational-numbers.html#2056" class="Function">commutative-ring-ℚ</a> <a id="2155" class="Symbol">=</a> <a id="2157" href="elementary-number-theory.multiplication-rational-numbers.html#7012" class="Function">commutative-mul-ℚ</a>
</pre>
### The inclusion of integers in the rationals is the initial ring homomorphism

<pre class="Agda"><a id="hom-ring-rational-ℤ"></a><a id="2269" href="elementary-number-theory.ring-of-rational-numbers.html#2269" class="Function">hom-ring-rational-ℤ</a> <a id="2289" class="Symbol">:</a> <a id="2291" href="ring-theory.homomorphisms-rings.html#3643" class="Function">hom-Ring</a> <a id="2300" href="elementary-number-theory.ring-of-integers.html#1087" class="Function">ℤ-Ring</a> <a id="2307" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a>
<a id="2314" href="elementary-number-theory.ring-of-rational-numbers.html#2269" class="Function">hom-ring-rational-ℤ</a> <a id="2334" class="Symbol">=</a>
  <a id="2338" class="Symbol">(</a> <a id="2340" href="elementary-number-theory.additive-group-of-rational-numbers.html#3231" class="Function">hom-add-rational-ℤ</a><a id="2358" class="Symbol">)</a> <a id="2360" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
  <a id="2364" class="Symbol">(</a> <a id="2366" class="Symbol">λ</a> <a id="2368" class="Symbol">{</a><a id="2369" href="elementary-number-theory.ring-of-rational-numbers.html#2369" class="Bound">x</a> <a id="2371" href="elementary-number-theory.ring-of-rational-numbers.html#2371" class="Bound">y</a><a id="2372" class="Symbol">}</a> <a id="2374" class="Symbol">→</a> <a id="2376" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="2380" class="Symbol">(</a><a id="2381" href="elementary-number-theory.multiplication-rational-numbers.html#12344" class="Function">mul-rational-ℤ</a> <a id="2396" href="elementary-number-theory.ring-of-rational-numbers.html#2369" class="Bound">x</a> <a id="2398" href="elementary-number-theory.ring-of-rational-numbers.html#2371" class="Bound">y</a><a id="2399" class="Symbol">))</a> <a id="2402" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
  <a id="2406" class="Symbol">(</a> <a id="2408" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="2412" class="Symbol">)</a>

<a id="2415" class="Keyword">abstract</a>
  <a id="htpy-map-initial-hom-ring-rational-ℤ"></a><a id="2426" href="elementary-number-theory.ring-of-rational-numbers.html#2426" class="Function">htpy-map-initial-hom-ring-rational-ℤ</a> <a id="2463" class="Symbol">:</a>
    <a id="2469" href="elementary-number-theory.ring-of-integers.html#3367" class="Function">map-initial-hom-Ring</a> <a id="2490" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a> <a id="2497" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="2499" href="elementary-number-theory.rational-numbers.html#3128" class="Function">rational-ℤ</a>
  <a id="2512" href="elementary-number-theory.ring-of-rational-numbers.html#2426" class="Function">htpy-map-initial-hom-ring-rational-ℤ</a> <a id="2549" class="Symbol">=</a>
    <a id="2555" href="elementary-number-theory.ring-of-integers.html#4791" class="Function">htpy-initial-hom-Ring</a> <a id="2577" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a> <a id="2584" href="elementary-number-theory.ring-of-rational-numbers.html#2269" class="Function">hom-ring-rational-ℤ</a>

  <a id="eq-initial-hom-ring-rational-ℤ"></a><a id="2607" href="elementary-number-theory.ring-of-rational-numbers.html#2607" class="Function">eq-initial-hom-ring-rational-ℤ</a> <a id="2638" class="Symbol">:</a> <a id="2640" href="elementary-number-theory.ring-of-integers.html#4413" class="Function">initial-hom-Ring</a> <a id="2657" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a> <a id="2664" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2666" href="elementary-number-theory.ring-of-rational-numbers.html#2269" class="Function">hom-ring-rational-ℤ</a>
  <a id="2688" href="elementary-number-theory.ring-of-rational-numbers.html#2607" class="Function">eq-initial-hom-ring-rational-ℤ</a> <a id="2719" class="Symbol">=</a>
    <a id="2725" href="elementary-number-theory.ring-of-integers.html#5169" class="Function">contraction-initial-hom-Ring</a> <a id="2754" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a> <a id="2761" href="elementary-number-theory.ring-of-rational-numbers.html#2269" class="Function">hom-ring-rational-ℤ</a>
</pre>
### The positive integers are invertible in ℚ

<pre class="Agda"><a id="2841" class="Keyword">abstract</a>
  <a id="inverts-positive-integers-rational-ℤ"></a><a id="2852" href="elementary-number-theory.ring-of-rational-numbers.html#2852" class="Function">inverts-positive-integers-rational-ℤ</a> <a id="2889" class="Symbol">:</a>
    <a id="2895" href="ring-theory.localizations-rings.html#7562" class="Function">inverts-subset-hom-Ring</a>
      <a id="2925" class="Symbol">(</a> <a id="2927" href="elementary-number-theory.ring-of-integers.html#1087" class="Function">ℤ-Ring</a><a id="2933" class="Symbol">)</a>
      <a id="2941" class="Symbol">(</a> <a id="2943" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a><a id="2949" class="Symbol">)</a>
      <a id="2957" class="Symbol">(</a> <a id="2959" href="elementary-number-theory.positive-integers.html#2306" class="Function">subtype-positive-ℤ</a><a id="2977" class="Symbol">)</a>
      <a id="2985" class="Symbol">(</a> <a id="2987" href="elementary-number-theory.ring-of-rational-numbers.html#2269" class="Function">hom-ring-rational-ℤ</a><a id="3006" class="Symbol">)</a>
  <a id="3010" href="elementary-number-theory.ring-of-rational-numbers.html#2852" class="Function">inverts-positive-integers-rational-ℤ</a> <a id="3047" href="elementary-number-theory.ring-of-rational-numbers.html#3047" class="Bound">k</a> <a id="3049" href="elementary-number-theory.ring-of-rational-numbers.html#3049" class="Bound">k&gt;0</a> <a id="3053" class="Symbol">=</a>
    <a id="3059" class="Symbol">(</a> <a id="3061" href="elementary-number-theory.unit-fractions-rational-numbers.html#2577" class="Function">reciprocal-rational-ℤ⁺</a> <a id="3084" class="Symbol">(</a><a id="3085" href="elementary-number-theory.ring-of-rational-numbers.html#3047" class="Bound">k</a> <a id="3087" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3089" href="elementary-number-theory.ring-of-rational-numbers.html#3049" class="Bound">k&gt;0</a><a id="3092" class="Symbol">))</a> <a id="3095" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="3101" class="Symbol">(</a> <a id="3103" href="elementary-number-theory.unit-fractions-rational-numbers.html#7449" class="Function">right-inverse-law-reciprocal-rational-ℤ⁺</a> <a id="3144" class="Symbol">(</a><a id="3145" href="elementary-number-theory.ring-of-rational-numbers.html#3047" class="Bound">k</a> <a id="3147" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3149" href="elementary-number-theory.ring-of-rational-numbers.html#3049" class="Bound">k&gt;0</a><a id="3152" class="Symbol">)</a> <a id="3154" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="3162" href="elementary-number-theory.unit-fractions-rational-numbers.html#6900" class="Function">left-inverse-law-reciprocal-rational-ℤ⁺</a> <a id="3202" class="Symbol">(</a><a id="3203" href="elementary-number-theory.ring-of-rational-numbers.html#3047" class="Bound">k</a> <a id="3205" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3207" href="elementary-number-theory.ring-of-rational-numbers.html#3049" class="Bound">k&gt;0</a><a id="3210" class="Symbol">))</a>
</pre>
### Any ring homomorphism from ℚ inverts the positive integers

<pre class="Agda"><a id="3290" class="Keyword">module</a> <a id="3297" href="elementary-number-theory.ring-of-rational-numbers.html#3297" class="Module">_</a>
  <a id="3301" class="Symbol">{</a><a id="3302" href="elementary-number-theory.ring-of-rational-numbers.html#3302" class="Bound">l</a> <a id="3304" class="Symbol">:</a> <a id="3306" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3311" class="Symbol">}</a> <a id="3313" class="Symbol">(</a><a id="3314" href="elementary-number-theory.ring-of-rational-numbers.html#3314" class="Bound">R</a> <a id="3316" class="Symbol">:</a> <a id="3318" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="3323" href="elementary-number-theory.ring-of-rational-numbers.html#3302" class="Bound">l</a><a id="3324" class="Symbol">)</a> <a id="3326" class="Symbol">(</a><a id="3327" href="elementary-number-theory.ring-of-rational-numbers.html#3327" class="Bound">f</a> <a id="3329" class="Symbol">:</a> <a id="3331" href="ring-theory.homomorphisms-rings.html#3643" class="Function">hom-Ring</a> <a id="3340" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a> <a id="3347" href="elementary-number-theory.ring-of-rational-numbers.html#3314" class="Bound">R</a><a id="3348" class="Symbol">)</a>
  <a id="3352" class="Keyword">where</a>

  <a id="3361" class="Keyword">abstract</a>
    <a id="3374" href="elementary-number-theory.ring-of-rational-numbers.html#3374" class="Function">inverts-positive-integers-rational-hom-Ring</a> <a id="3418" class="Symbol">:</a>
      <a id="3426" href="ring-theory.localizations-rings.html#7562" class="Function">inverts-subset-hom-Ring</a>
        <a id="3458" class="Symbol">(</a> <a id="3460" href="elementary-number-theory.ring-of-integers.html#1087" class="Function">ℤ-Ring</a><a id="3466" class="Symbol">)</a>
        <a id="3476" class="Symbol">(</a> <a id="3478" href="elementary-number-theory.ring-of-rational-numbers.html#3314" class="Bound">R</a><a id="3479" class="Symbol">)</a>
        <a id="3489" class="Symbol">(</a> <a id="3491" href="elementary-number-theory.positive-integers.html#2306" class="Function">subtype-positive-ℤ</a><a id="3509" class="Symbol">)</a>
        <a id="3519" class="Symbol">(</a> <a id="3521" href="ring-theory.homomorphisms-rings.html#8247" class="Function">comp-hom-Ring</a> <a id="3535" href="elementary-number-theory.ring-of-integers.html#1087" class="Function">ℤ-Ring</a> <a id="3542" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a> <a id="3549" href="elementary-number-theory.ring-of-rational-numbers.html#3314" class="Bound">R</a> <a id="3551" href="elementary-number-theory.ring-of-rational-numbers.html#3327" class="Bound">f</a> <a id="3553" href="elementary-number-theory.ring-of-rational-numbers.html#2269" class="Function">hom-ring-rational-ℤ</a><a id="3572" class="Symbol">)</a>
    <a id="3578" href="elementary-number-theory.ring-of-rational-numbers.html#3374" class="Function">inverts-positive-integers-rational-hom-Ring</a> <a id="3622" href="elementary-number-theory.ring-of-rational-numbers.html#3622" class="Bound">k</a> <a id="3624" href="elementary-number-theory.ring-of-rational-numbers.html#3624" class="Bound">k&gt;0</a> <a id="3628" class="Symbol">=</a>
      <a id="3636" href="ring-theory.homomorphisms-rings.html#12385" class="Function">preserves-invertible-elements-hom-Ring</a>
        <a id="3683" class="Symbol">(</a> <a id="3685" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a><a id="3691" class="Symbol">)</a>
        <a id="3701" class="Symbol">(</a> <a id="3703" href="elementary-number-theory.ring-of-rational-numbers.html#3314" class="Bound">R</a><a id="3704" class="Symbol">)</a>
        <a id="3714" class="Symbol">(</a> <a id="3716" href="elementary-number-theory.ring-of-rational-numbers.html#3327" class="Bound">f</a><a id="3717" class="Symbol">)</a>
        <a id="3727" class="Symbol">(</a> <a id="3729" href="elementary-number-theory.ring-of-rational-numbers.html#2852" class="Function">inverts-positive-integers-rational-ℤ</a> <a id="3766" href="elementary-number-theory.ring-of-rational-numbers.html#3622" class="Bound">k</a> <a id="3768" href="elementary-number-theory.ring-of-rational-numbers.html#3624" class="Bound">k&gt;0</a><a id="3771" class="Symbol">)</a>
</pre>
## See also

- [`ring-extension-rational-numbers-of-rational-numbers`](elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.md):
  the trivial
  [ring extension of `ℚ`](ring-theory.ring-extensions-rational-numbers.md) where
  it is proven that `ℚ` is the
  [localization](ring-theory.localizations-rings.md) of `ℤ` at `ℤ⁺`.
