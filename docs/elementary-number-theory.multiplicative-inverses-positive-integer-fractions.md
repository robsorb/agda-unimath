# Multiplicative inverses of positive integer fractions

<pre class="Agda"><a id="66" class="Keyword">module</a> <a id="73" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html" class="Module">elementary-number-theory.multiplicative-inverses-positive-integer-fractions</a> <a id="149" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="205" class="Keyword">open</a> <a id="210" class="Keyword">import</a> <a id="217" href="elementary-number-theory.greatest-common-divisor-integers.html" class="Module">elementary-number-theory.greatest-common-divisor-integers</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="elementary-number-theory.integer-fractions.html" class="Module">elementary-number-theory.integer-fractions</a>
<a id="330" class="Keyword">open</a> <a id="335" class="Keyword">import</a> <a id="342" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a>
<a id="376" class="Keyword">open</a> <a id="381" class="Keyword">import</a> <a id="388" href="elementary-number-theory.multiplication-integer-fractions.html" class="Module">elementary-number-theory.multiplication-integer-fractions</a>
<a id="446" class="Keyword">open</a> <a id="451" class="Keyword">import</a> <a id="458" href="elementary-number-theory.multiplication-integers.html" class="Module">elementary-number-theory.multiplication-integers</a>
<a id="507" class="Keyword">open</a> <a id="512" class="Keyword">import</a> <a id="519" href="elementary-number-theory.positive-integer-fractions.html" class="Module">elementary-number-theory.positive-integer-fractions</a>
<a id="571" class="Keyword">open</a> <a id="576" class="Keyword">import</a> <a id="583" href="elementary-number-theory.reduced-integer-fractions.html" class="Module">elementary-number-theory.reduced-integer-fractions</a>

<a id="635" class="Keyword">open</a> <a id="640" class="Keyword">import</a> <a id="647" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="679" class="Keyword">open</a> <a id="684" class="Keyword">import</a> <a id="691" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="717" class="Keyword">open</a> <a id="722" class="Keyword">import</a> <a id="729" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
</pre>
</details>

## Idea

The integer fraction obtained by swapping the numerator and the denominator of a
[positive integer fraction](elementary-number-theory.positive-integer-fractions.md)
is a
[multiplicative](elementary-number-theory.multiplication-integer-fractions.md)
inverse of the original fraction up to the canonical similarity relation on
[integer fractions](elementary-number-theory.integer-fractions.md): its
multiplication with the original fraction is similar to one.

## Definitions

### The inverse of a positive integer fraction

<pre class="Agda"><a id="1329" class="Keyword">module</a> <a id="1336" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1336" class="Module">_</a>
  <a id="1340" class="Symbol">(</a><a id="1341" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1341" class="Bound">x</a> <a id="1343" class="Symbol">:</a> <a id="1345" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="1355" class="Symbol">)</a> <a id="1357" class="Symbol">(</a><a id="1358" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1358" class="Bound">H</a> <a id="1360" class="Symbol">:</a> <a id="1362" href="elementary-number-theory.positive-integer-fractions.html#1224" class="Function">is-positive-fraction-ℤ</a> <a id="1385" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1341" class="Bound">x</a><a id="1386" class="Symbol">)</a>
  <a id="1390" class="Keyword">where</a>

  <a id="1399" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1399" class="Function">inv-is-positive-fraction-ℤ</a> <a id="1426" class="Symbol">:</a> <a id="1428" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a>
  <a id="1441" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1445" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1399" class="Function">inv-is-positive-fraction-ℤ</a> <a id="1472" class="Symbol">=</a> <a id="1474" href="elementary-number-theory.integer-fractions.html#1640" class="Function">denominator-fraction-ℤ</a> <a id="1497" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1341" class="Bound">x</a>
  <a id="1501" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1505" class="Symbol">(</a><a id="1506" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1510" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1399" class="Function">inv-is-positive-fraction-ℤ</a><a id="1536" class="Symbol">)</a> <a id="1538" class="Symbol">=</a> <a id="1540" href="elementary-number-theory.integer-fractions.html#1422" class="Function">numerator-fraction-ℤ</a> <a id="1561" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1341" class="Bound">x</a>
  <a id="1565" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1569" class="Symbol">(</a><a id="1570" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1574" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1399" class="Function">inv-is-positive-fraction-ℤ</a><a id="1600" class="Symbol">)</a> <a id="1602" class="Symbol">=</a> <a id="1604" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1358" class="Bound">H</a>
</pre>
## Properties

### The inverse of a positive reduced integer fraction is reduced

<pre class="Agda"><a id="1701" class="Keyword">module</a> <a id="1708" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1708" class="Module">_</a>
  <a id="1712" class="Symbol">(</a><a id="1713" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1713" class="Bound">x</a> <a id="1715" class="Symbol">:</a> <a id="1717" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="1727" class="Symbol">)</a> <a id="1729" class="Symbol">(</a><a id="1730" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1730" class="Bound">P</a> <a id="1732" class="Symbol">:</a> <a id="1734" href="elementary-number-theory.positive-integer-fractions.html#1224" class="Function">is-positive-fraction-ℤ</a> <a id="1757" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1713" class="Bound">x</a><a id="1758" class="Symbol">)</a>
  <a id="1762" class="Keyword">where</a>

  <a id="1771" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1771" class="Function">is-reduced-inv-is-positive-fraction-ℤ</a> <a id="1809" class="Symbol">:</a>
    <a id="1815" href="elementary-number-theory.reduced-integer-fractions.html#1557" class="Function">is-reduced-fraction-ℤ</a> <a id="1837" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1713" class="Bound">x</a> <a id="1839" class="Symbol">→</a>
    <a id="1845" href="elementary-number-theory.reduced-integer-fractions.html#1557" class="Function">is-reduced-fraction-ℤ</a> <a id="1867" class="Symbol">(</a><a id="1868" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1399" class="Function">inv-is-positive-fraction-ℤ</a> <a id="1895" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1713" class="Bound">x</a> <a id="1897" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1730" class="Bound">P</a><a id="1898" class="Symbol">)</a>
  <a id="1902" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1771" class="Function">is-reduced-inv-is-positive-fraction-ℤ</a> <a id="1940" class="Symbol">=</a>
    <a id="1946" href="foundation.transport-along-identifications.html#1082" class="Function">inv-tr</a>
      <a id="1959" class="Symbol">(</a> <a id="1961" href="elementary-number-theory.integers.html#1887" class="Function">is-one-ℤ</a><a id="1969" class="Symbol">)</a>
      <a id="1977" class="Symbol">(</a> <a id="1979" href="elementary-number-theory.greatest-common-divisor-integers.html#10224" class="Function">is-commutative-gcd-ℤ</a>
        <a id="2008" class="Symbol">(</a> <a id="2010" href="elementary-number-theory.integer-fractions.html#1640" class="Function">denominator-fraction-ℤ</a> <a id="2033" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1713" class="Bound">x</a><a id="2034" class="Symbol">)</a>
        <a id="2044" class="Symbol">(</a> <a id="2046" href="elementary-number-theory.integer-fractions.html#1422" class="Function">numerator-fraction-ℤ</a> <a id="2067" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1713" class="Bound">x</a><a id="2068" class="Symbol">))</a>
</pre>
### The multiplication of a positive integer fraction with its inverse is similar to one

<pre class="Agda"><a id="2174" class="Keyword">module</a> <a id="2181" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2181" class="Module">_</a>
  <a id="2185" class="Symbol">(</a><a id="2186" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2186" class="Bound">x</a> <a id="2188" class="Symbol">:</a> <a id="2190" href="elementary-number-theory.integer-fractions.html#1326" class="Function">fraction-ℤ</a><a id="2200" class="Symbol">)</a> <a id="2202" class="Symbol">(</a><a id="2203" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2203" class="Bound">P</a> <a id="2205" class="Symbol">:</a> <a id="2207" href="elementary-number-theory.positive-integer-fractions.html#1224" class="Function">is-positive-fraction-ℤ</a> <a id="2230" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2186" class="Bound">x</a><a id="2231" class="Symbol">)</a>
  <a id="2235" class="Keyword">where</a>

  <a id="2244" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2244" class="Function">left-inverse-law-mul-is-positive-fraction-ℤ</a> <a id="2288" class="Symbol">:</a>
    <a id="2294" href="elementary-number-theory.integer-fractions.html#4242" class="Function">sim-fraction-ℤ</a>
      <a id="2315" class="Symbol">(</a><a id="2316" href="elementary-number-theory.multiplication-integer-fractions.html#1310" class="Function">mul-fraction-ℤ</a> <a id="2331" class="Symbol">(</a><a id="2332" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1399" class="Function">inv-is-positive-fraction-ℤ</a> <a id="2359" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2186" class="Bound">x</a> <a id="2361" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2203" class="Bound">P</a><a id="2362" class="Symbol">)</a> <a id="2364" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2186" class="Bound">x</a><a id="2365" class="Symbol">)</a>
      <a id="2373" class="Symbol">(</a><a id="2374" href="elementary-number-theory.integer-fractions.html#2543" class="Function">one-fraction-ℤ</a><a id="2388" class="Symbol">)</a>
  <a id="2392" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2244" class="Function">left-inverse-law-mul-is-positive-fraction-ℤ</a> <a id="2436" class="Symbol">=</a>
    <a id="2442" class="Symbol">(</a> <a id="2444" href="elementary-number-theory.multiplication-integers.html#3636" class="Function">right-unit-law-mul-ℤ</a> <a id="2465" class="Symbol">_)</a> <a id="2468" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
    <a id="2474" class="Symbol">(</a> <a id="2476" href="elementary-number-theory.multiplication-integers.html#12689" class="Function">commutative-mul-ℤ</a>
      <a id="2500" class="Symbol">(</a> <a id="2502" href="elementary-number-theory.integer-fractions.html#1640" class="Function">denominator-fraction-ℤ</a> <a id="2525" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2186" class="Bound">x</a><a id="2526" class="Symbol">)</a>
      <a id="2534" class="Symbol">(</a> <a id="2536" href="elementary-number-theory.integer-fractions.html#1422" class="Function">numerator-fraction-ℤ</a> <a id="2557" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2186" class="Bound">x</a><a id="2558" class="Symbol">))</a> <a id="2561" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
    <a id="2567" class="Symbol">(</a> <a id="2569" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="2573" class="Symbol">(</a><a id="2574" href="elementary-number-theory.multiplication-integers.html#3559" class="Function">left-unit-law-mul-ℤ</a> <a id="2594" class="Symbol">_))</a>

  <a id="2601" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2601" class="Function">right-inverse-law-mul-is-positive-fraction-ℤ</a> <a id="2646" class="Symbol">:</a>
    <a id="2652" href="elementary-number-theory.integer-fractions.html#4242" class="Function">sim-fraction-ℤ</a>
      <a id="2673" class="Symbol">(</a><a id="2674" href="elementary-number-theory.multiplication-integer-fractions.html#1310" class="Function">mul-fraction-ℤ</a> <a id="2689" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2186" class="Bound">x</a> <a id="2691" class="Symbol">(</a><a id="2692" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#1399" class="Function">inv-is-positive-fraction-ℤ</a> <a id="2719" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2186" class="Bound">x</a> <a id="2721" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2203" class="Bound">P</a><a id="2722" class="Symbol">))</a>
      <a id="2731" class="Symbol">(</a><a id="2732" href="elementary-number-theory.integer-fractions.html#2543" class="Function">one-fraction-ℤ</a><a id="2746" class="Symbol">)</a>
  <a id="2750" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2601" class="Function">right-inverse-law-mul-is-positive-fraction-ℤ</a> <a id="2795" class="Symbol">=</a>
    <a id="2801" class="Symbol">(</a> <a id="2803" href="elementary-number-theory.multiplication-integers.html#3636" class="Function">right-unit-law-mul-ℤ</a> <a id="2824" class="Symbol">_)</a> <a id="2827" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
    <a id="2833" class="Symbol">(</a> <a id="2835" href="elementary-number-theory.multiplication-integers.html#12689" class="Function">commutative-mul-ℤ</a>
      <a id="2859" class="Symbol">(</a> <a id="2861" href="elementary-number-theory.integer-fractions.html#1422" class="Function">numerator-fraction-ℤ</a> <a id="2882" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2186" class="Bound">x</a><a id="2883" class="Symbol">)</a>
      <a id="2891" class="Symbol">(</a> <a id="2893" href="elementary-number-theory.integer-fractions.html#1640" class="Function">denominator-fraction-ℤ</a> <a id="2916" href="elementary-number-theory.multiplicative-inverses-positive-integer-fractions.html#2186" class="Bound">x</a><a id="2917" class="Symbol">))</a> <a id="2920" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
    <a id="2926" class="Symbol">(</a> <a id="2928" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="2932" class="Symbol">(</a><a id="2933" href="elementary-number-theory.multiplication-integers.html#3559" class="Function">left-unit-law-mul-ℤ</a> <a id="2953" class="Symbol">_))</a>
</pre>