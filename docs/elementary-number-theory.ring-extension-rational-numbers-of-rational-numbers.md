# The ring extension of rational numbers of the ring of rational numbers

<pre class="Agda"><a id="83" class="Keyword">module</a> <a id="90" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html" class="Module">elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers</a> <a id="167" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="elementary-number-theory.positive-integers.html" class="Module">elementary-number-theory.positive-integers</a>
<a id="278" class="Keyword">open</a> <a id="283" class="Keyword">import</a> <a id="290" href="elementary-number-theory.ring-of-integers.html" class="Module">elementary-number-theory.ring-of-integers</a>
<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="elementary-number-theory.ring-of-rational-numbers.html" class="Module">elementary-number-theory.ring-of-rational-numbers</a>

<a id="395" class="Keyword">open</a> <a id="400" class="Keyword">import</a> <a id="407" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="437" class="Keyword">open</a> <a id="442" class="Keyword">import</a> <a id="449" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="481" class="Keyword">open</a> <a id="486" class="Keyword">import</a> <a id="493" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="525" class="Keyword">open</a> <a id="530" class="Keyword">import</a> <a id="537" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="557" class="Keyword">open</a> <a id="562" class="Keyword">import</a> <a id="569" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="612" class="Keyword">open</a> <a id="617" class="Keyword">import</a> <a id="624" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="652" class="Keyword">open</a> <a id="657" class="Keyword">import</a> <a id="664" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html" class="Module">ring-theory.homomorphisms-ring-extensions-rational-numbers</a>
<a id="723" class="Keyword">open</a> <a id="728" class="Keyword">import</a> <a id="735" href="ring-theory.homomorphisms-rings.html" class="Module">ring-theory.homomorphisms-rings</a>
<a id="767" class="Keyword">open</a> <a id="772" class="Keyword">import</a> <a id="779" href="ring-theory.localizations-rings.html" class="Module">ring-theory.localizations-rings</a>
<a id="811" class="Keyword">open</a> <a id="816" class="Keyword">import</a> <a id="823" href="ring-theory.ring-extensions-rational-numbers.html" class="Module">ring-theory.ring-extensions-rational-numbers</a>
<a id="868" class="Keyword">open</a> <a id="873" class="Keyword">import</a> <a id="880" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
</details>

## Idea

The
[ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md)
is a [ring extension of `ℚ`](ring-theory.ring-extensions-rational-numbers.md) so
`ℚ` is the initial ring extension of `ℚ`: the type of
[ring homomorphisms](ring-theory.homomorphisms-rings.md) from `ℚ` to a ring
extension of `ℚ` is [contractible](foundation-core.contractible-types.md).

As a corollary, `ℚ` is the [localization](ring-theory.localizations-rings.md) of
`ℤ` at `ℤ⁺`: any ring homomorphism `ℤ → R` that inverts the positive integers
extends to a ring homomorphism `ℚ → R`.

## Definition

### `ℚ` is a rational extension of itself

<pre class="Agda"><a id="is-rational-extension-ring-ℚ"></a><a id="1562" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#1562" class="Function">is-rational-extension-ring-ℚ</a> <a id="1591" class="Symbol">:</a> <a id="1593" href="ring-theory.ring-extensions-rational-numbers.html#3240" class="Function">is-rational-extension-Ring</a> <a id="1620" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a>
<a id="1627" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#1562" class="Function">is-rational-extension-ring-ℚ</a> <a id="1656" class="Symbol">=</a>
  <a id="1660" href="ring-theory.ring-extensions-rational-numbers.html#12385" class="Function">is-rational-extension-has-rational-hom-Ring</a>
    <a id="1708" class="Symbol">(</a> <a id="1710" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a><a id="1716" class="Symbol">)</a>
    <a id="1722" class="Symbol">(</a> <a id="1724" href="ring-theory.homomorphisms-rings.html#6541" class="Function">id-hom-Ring</a> <a id="1736" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a><a id="1742" class="Symbol">)</a>

<a id="rational-extension-ring-ℚ"></a><a id="1745" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#1745" class="Function">rational-extension-ring-ℚ</a> <a id="1771" class="Symbol">:</a> <a id="1773" href="ring-theory.ring-extensions-rational-numbers.html#3568" class="Function">Rational-Extension-Ring</a> <a id="1797" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1803" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#1745" class="Function">rational-extension-ring-ℚ</a> <a id="1829" class="Symbol">=</a>
  <a id="1833" class="Symbol">(</a> <a id="1835" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a> <a id="1842" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1844" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#1562" class="Function">is-rational-extension-ring-ℚ</a><a id="1872" class="Symbol">)</a>
</pre>
## Properties

### The ring of rational numbers is the initial ring extension of `ℚ`

<pre class="Agda"><a id="1973" class="Keyword">module</a> <a id="1980" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#1980" class="Module">_</a>
  <a id="1984" class="Symbol">{</a><a id="1985" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#1985" class="Bound">l</a> <a id="1987" class="Symbol">:</a> <a id="1989" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1994" class="Symbol">}</a>
  <a id="1998" class="Keyword">where</a>

  <a id="2007" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2007" class="Function">is-initial-rational-extension-ring-ℚ</a> <a id="2044" class="Symbol">:</a>
    <a id="2050" class="Symbol">(</a><a id="2051" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2051" class="Bound">R</a> <a id="2053" class="Symbol">:</a> <a id="2055" href="ring-theory.ring-extensions-rational-numbers.html#3568" class="Function">Rational-Extension-Ring</a> <a id="2079" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#1985" class="Bound">l</a><a id="2080" class="Symbol">)</a> <a id="2082" class="Symbol">→</a>
    <a id="2088" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="2097" class="Symbol">(</a><a id="2098" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#863" class="Function">hom-Rational-Extension-Ring</a> <a id="2126" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#1745" class="Function">rational-extension-ring-ℚ</a> <a id="2152" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2051" class="Bound">R</a><a id="2153" class="Symbol">)</a>
  <a id="2157" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2007" class="Function">is-initial-rational-extension-ring-ℚ</a> <a id="2194" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2194" class="Bound">R</a> <a id="2196" class="Symbol">=</a>
    <a id="2202" href="ring-theory.ring-extensions-rational-numbers.html#44642" class="Function">is-contr-rational-hom-Rational-Extension-Ring</a> <a id="2248" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2194" class="Bound">R</a>
</pre>
### The ring of rational numbers is the localization of the ring of integers at `ℤ⁺`

<pre class="Agda"><a id="2349" class="Keyword">module</a> <a id="2356" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2356" class="Module">_</a>
  <a id="2360" class="Symbol">{</a><a id="2361" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2361" class="Bound">l</a> <a id="2363" class="Symbol">:</a> <a id="2365" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2370" class="Symbol">}</a>
  <a id="2374" class="Keyword">where</a>

  <a id="2383" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2383" class="Function">universal-property-localization-positive-integers-ring-ℚ</a> <a id="2440" class="Symbol">:</a>
    <a id="2446" href="ring-theory.localizations-rings.html#10562" class="Function">universal-property-localization-subset-Ring</a>
      <a id="2496" class="Symbol">(</a> <a id="2498" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2361" class="Bound">l</a><a id="2499" class="Symbol">)</a>
      <a id="2507" class="Symbol">(</a> <a id="2509" href="elementary-number-theory.ring-of-integers.html#1087" class="Function">ℤ-Ring</a><a id="2515" class="Symbol">)</a>
      <a id="2523" class="Symbol">(</a> <a id="2525" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a><a id="2531" class="Symbol">)</a>
      <a id="2539" class="Symbol">(</a> <a id="2541" href="elementary-number-theory.positive-integers.html#2306" class="Function">subtype-positive-ℤ</a><a id="2559" class="Symbol">)</a>
      <a id="2567" class="Symbol">(</a> <a id="2569" href="elementary-number-theory.ring-of-integers.html#4413" class="Function">initial-hom-Ring</a> <a id="2586" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a><a id="2592" class="Symbol">)</a>
      <a id="2600" class="Symbol">(</a> <a id="2602" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#1562" class="Function">is-rational-extension-ring-ℚ</a><a id="2630" class="Symbol">)</a>
  <a id="2634" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2383" class="Function">universal-property-localization-positive-integers-ring-ℚ</a> <a id="2691" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2691" class="Bound">T</a> <a id="2693" class="Symbol">=</a>
    <a id="2699" href="foundation.logical-equivalences.html#4351" class="Function">is-equiv-has-converse-is-prop</a>
      <a id="2735" class="Symbol">(</a> <a id="2737" href="ring-theory.ring-extensions-rational-numbers.html#39875" class="Function">is-prop-has-rational-hom-Ring</a> <a id="2767" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2691" class="Bound">T</a><a id="2768" class="Symbol">)</a>
      <a id="2776" class="Symbol">(</a> <a id="2778" href="foundation-core.subtypes.html#7918" class="Function">is-prop-type-subtype</a>
        <a id="2807" class="Symbol">(</a> <a id="2809" href="ring-theory.localizations-rings.html#8110" class="Function">inverts-subset-prop-hom-Ring</a> <a id="2838" href="elementary-number-theory.ring-of-integers.html#1087" class="Function">ℤ-Ring</a> <a id="2845" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2691" class="Bound">T</a> <a id="2847" href="elementary-number-theory.positive-integers.html#2306" class="Function">subtype-positive-ℤ</a><a id="2865" class="Symbol">)</a>
        <a id="2875" class="Symbol">(</a> <a id="2877" href="foundation-core.contractible-types.html#7620" class="Function">is-prop-is-contr</a> <a id="2894" class="Symbol">(</a><a id="2895" href="elementary-number-theory.ring-of-integers.html#5427" class="Function">is-initial-ℤ-Ring</a> <a id="2913" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2691" class="Bound">T</a><a id="2914" class="Symbol">)))</a>
      <a id="2924" class="Symbol">(</a> <a id="2926" class="Symbol">λ</a> <a id="2928" class="Symbol">(</a><a id="2929" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2929" class="Bound">f</a> <a id="2931" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2933" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2933" class="Bound">H</a><a id="2934" class="Symbol">)</a> <a id="2936" class="Symbol">→</a>
        <a id="2946" href="ring-theory.ring-extensions-rational-numbers.html#44086" class="Function">initial-hom-Rational-Extension-Ring</a>
          <a id="2992" class="Symbol">(</a> <a id="2994" class="Symbol">(</a> <a id="2996" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2691" class="Bound">T</a><a id="2997" class="Symbol">)</a> <a id="2999" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
            <a id="3013" class="Symbol">(</a> <a id="3015" href="foundation.transport-along-identifications.html#1082" class="Function">inv-tr</a>
              <a id="3036" class="Symbol">(</a> <a id="3038" href="ring-theory.localizations-rings.html#7562" class="Function">inverts-subset-hom-Ring</a> <a id="3062" href="elementary-number-theory.ring-of-integers.html#1087" class="Function">ℤ-Ring</a> <a id="3069" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2691" class="Bound">T</a> <a id="3071" href="elementary-number-theory.positive-integers.html#2306" class="Function">subtype-positive-ℤ</a><a id="3089" class="Symbol">)</a>
              <a id="3105" class="Symbol">(</a> <a id="3107" href="elementary-number-theory.ring-of-integers.html#5169" class="Function">contraction-initial-hom-Ring</a> <a id="3136" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2691" class="Bound">T</a> <a id="3138" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2929" class="Bound">f</a><a id="3139" class="Symbol">)</a>
              <a id="3155" class="Symbol">(</a> <a id="3157" href="elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.html#2933" class="Bound">H</a><a id="3158" class="Symbol">))))</a>
</pre>