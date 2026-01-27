# Wiedijk's 100 Theorems

This file records formalized results from
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s
[_Formalizing 100 Theorems_](https://www.cs.ru.nl/~freek/100/)
{{#cite 100theorems}}.

<pre class="Agda"><a id="214" class="Keyword">module</a> <a id="221" href="literature.100-theorems.html" class="Module">literature.100-theorems</a> <a id="245" class="Keyword">where</a>
</pre>
## The list

### 3. The denumerability of the rational numbers {#3}

**Author:** [Fredrik Bakke](https://www.ntnu.edu/employees/fredrik.bakke)

<pre class="Agda"><a id="408" class="Keyword">open</a> <a id="413" class="Keyword">import</a> <a id="420" href="elementary-number-theory.rational-numbers.html" class="Module">elementary-number-theory.rational-numbers</a> <a id="462" class="Keyword">using</a>
  <a id="470" class="Symbol">(</a> <a id="472" href="elementary-number-theory.rational-numbers.html#5941" class="Function">is-countable-ℚ</a><a id="486" class="Symbol">)</a>
</pre>
### 11. The infinitude of primes {#11}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

<pre class="Agda"><a id="600" class="Keyword">open</a> <a id="605" class="Keyword">import</a> <a id="612" href="elementary-number-theory.infinitude-of-primes.html" class="Module">elementary-number-theory.infinitude-of-primes</a> <a id="658" class="Keyword">using</a>
  <a id="666" class="Symbol">(</a> <a id="668" href="elementary-number-theory.infinitude-of-primes.html#5223" class="Function">infinitude-of-primes-ℕ</a><a id="690" class="Symbol">)</a>
</pre>
### 25. Schröder–Bernstein theorem {#25}

**Author:** [Elif Uskuplu](https://elifuskuplu.github.io)

**Note:** The formalization of the Cantor-Schröder-Bernstein theorem in
agda-unimath is a generalization of the statement to all types, i.e., it is not
restricted to sets. This generalization is originally due to Martin-Escardó,
hence we refer to the generalization as the Cantor-Schröder-Bernstein-Escardó
theorem.

<pre class="Agda"><a id="1123" class="Keyword">open</a> <a id="1128" class="Keyword">import</a> <a id="1135" href="foundation.cantor-schroder-bernstein-escardo.html" class="Module">foundation.cantor-schroder-bernstein-escardo</a> <a id="1180" class="Keyword">using</a>
  <a id="1188" class="Symbol">(</a> <a id="1190" href="foundation.cantor-schroder-bernstein-escardo.html#6045" class="Function">Cantor-Schröder-Bernstein-Escardó</a> <a id="1224" class="Symbol">;</a>
    <a id="1230" href="foundation.cantor-schroder-bernstein-escardo.html#6399" class="Function">Cantor-Schröder-Bernstein</a><a id="1255" class="Symbol">)</a>
</pre>
### 44. The binomial theorem {#44}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

<pre class="Agda"><a id="1365" class="Keyword">open</a> <a id="1370" class="Keyword">import</a> <a id="1377" href="commutative-algebra.binomial-theorem-commutative-rings.html" class="Module">commutative-algebra.binomial-theorem-commutative-rings</a> <a id="1432" class="Keyword">using</a>
  <a id="1440" class="Symbol">(</a> <a id="1442" href="commutative-algebra.binomial-theorem-commutative-rings.html#4353" class="Function">binomial-theorem-Commutative-Ring</a><a id="1475" class="Symbol">)</a>
<a id="1477" class="Keyword">open</a> <a id="1482" class="Keyword">import</a> <a id="1489" href="commutative-algebra.binomial-theorem-commutative-semirings.html" class="Module">commutative-algebra.binomial-theorem-commutative-semirings</a> <a id="1548" class="Keyword">using</a>
  <a id="1556" class="Symbol">(</a> <a id="1558" href="commutative-algebra.binomial-theorem-commutative-semirings.html#4543" class="Function">binomial-theorem-Commutative-Semiring</a><a id="1595" class="Symbol">)</a>
<a id="1597" class="Keyword">open</a> <a id="1602" class="Keyword">import</a> <a id="1609" href="ring-theory.binomial-theorem-rings.html" class="Module">ring-theory.binomial-theorem-rings</a> <a id="1644" class="Keyword">using</a>
  <a id="1652" class="Symbol">(</a> <a id="1654" href="ring-theory.binomial-theorem-rings.html#3588" class="Function">binomial-theorem-Ring</a><a id="1675" class="Symbol">)</a>
<a id="1677" class="Keyword">open</a> <a id="1682" class="Keyword">import</a> <a id="1689" href="ring-theory.binomial-theorem-semirings.html" class="Module">ring-theory.binomial-theorem-semirings</a> <a id="1728" class="Keyword">using</a>
  <a id="1736" class="Symbol">(</a> <a id="1738" href="ring-theory.binomial-theorem-semirings.html#13317" class="Function">binomial-theorem-Semiring</a><a id="1763" class="Symbol">)</a>
<a id="1765" class="Keyword">open</a> <a id="1770" class="Keyword">import</a> <a id="1777" href="elementary-number-theory.binomial-theorem-integers.html" class="Module">elementary-number-theory.binomial-theorem-integers</a> <a id="1828" class="Keyword">using</a>
  <a id="1836" class="Symbol">(</a> <a id="1838" href="elementary-number-theory.binomial-theorem-integers.html#2836" class="Function">binomial-theorem-ℤ</a><a id="1856" class="Symbol">)</a>
<a id="1858" class="Keyword">open</a> <a id="1863" class="Keyword">import</a> <a id="1870" href="elementary-number-theory.binomial-theorem-natural-numbers.html" class="Module">elementary-number-theory.binomial-theorem-natural-numbers</a> <a id="1928" class="Keyword">using</a>
  <a id="1936" class="Symbol">(</a> <a id="1938" href="elementary-number-theory.binomial-theorem-natural-numbers.html#2929" class="Function">binomial-theorem-ℕ</a><a id="1956" class="Symbol">)</a>
</pre>
### 52. The number of subsets of a set {#52}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

<pre class="Agda"><a id="2076" class="Keyword">open</a> <a id="2081" class="Keyword">import</a> <a id="2088" href="univalent-combinatorics.decidable-subtypes.html" class="Module">univalent-combinatorics.decidable-subtypes</a> <a id="2131" class="Keyword">using</a>
  <a id="2139" class="Symbol">(</a> <a id="2141" href="univalent-combinatorics.decidable-subtypes.html#3470" class="Function">number-of-elements-decidable-subtype-is-finite</a><a id="2187" class="Symbol">)</a>
</pre>
### 58. Formula for the number of combinations {#58}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

<pre class="Agda"><a id="2315" class="Keyword">open</a> <a id="2320" class="Keyword">import</a> <a id="2327" href="univalent-combinatorics.binomial-types.html" class="Module">univalent-combinatorics.binomial-types</a> <a id="2366" class="Keyword">using</a>
  <a id="2374" class="Symbol">(</a> <a id="2376" href="univalent-combinatorics.binomial-types.html#14488" class="Function">has-cardinality-binomial-type</a><a id="2405" class="Symbol">)</a>
</pre>
### 60. Bezout's lemma {#60}

**Author:** [Bryan Lu](https://blu-bird.github.io)

Note that the 60th theorem in Freek's list is listed as "Bezout's Theorem",
while the linked theorems are formalizations of Bezout's lemma, even though
these are different statements.

<pre class="Agda"><a id="2687" class="Keyword">open</a> <a id="2692" class="Keyword">import</a> <a id="2699" href="elementary-number-theory.bezouts-lemma-integers.html" class="Module">elementary-number-theory.bezouts-lemma-integers</a> <a id="2747" class="Keyword">using</a>
  <a id="2755" class="Symbol">(</a> <a id="2757" href="elementary-number-theory.bezouts-lemma-integers.html#9652" class="Function">bezouts-lemma-ℤ</a><a id="2772" class="Symbol">)</a>
<a id="2774" class="Keyword">open</a> <a id="2779" class="Keyword">import</a> <a id="2786" href="elementary-number-theory.bezouts-lemma-natural-numbers.html" class="Module">elementary-number-theory.bezouts-lemma-natural-numbers</a> <a id="2841" class="Keyword">using</a>
  <a id="2849" class="Symbol">(</a> <a id="2851" href="elementary-number-theory.bezouts-lemma-natural-numbers.html#70534" class="Function">bezouts-lemma-ℕ</a><a id="2866" class="Symbol">)</a>
</pre>
### 63. Cantor's theorem {#63}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

<pre class="Agda"><a id="2972" class="Keyword">open</a> <a id="2977" class="Keyword">import</a> <a id="2984" href="foundation.cantors-theorem.html" class="Module">foundation.cantors-theorem</a> <a id="3011" class="Keyword">using</a>
  <a id="3019" class="Symbol">(</a> <a id="3021" href="foundation.cantors-theorem.html#2668" class="Function">theorem-Cantor</a><a id="3035" class="Symbol">)</a>
</pre>
### 68. Sum of an arithmetic series {#68}

**Author:** [malarbol](http://www.github.com/malarbol)

<pre class="Agda"><a id="3149" class="Keyword">open</a> <a id="3154" class="Keyword">import</a> <a id="3161" href="elementary-number-theory.triangular-numbers.html" class="Module">elementary-number-theory.triangular-numbers</a> <a id="3205" class="Keyword">using</a>
  <a id="3213" class="Symbol">(</a> <a id="3215" href="elementary-number-theory.triangular-numbers.html#2429" class="Function">compute-triangular-number-ℕ</a><a id="3242" class="Symbol">)</a>
<a id="3244" class="Keyword">open</a> <a id="3249" class="Keyword">import</a> <a id="3256" href="ring-theory.arithmetic-series-semirings.html" class="Module">ring-theory.arithmetic-series-semirings</a> <a id="3296" class="Keyword">using</a>
  <a id="3304" class="Symbol">(</a> <a id="3306" href="ring-theory.arithmetic-series-semirings.html#4824" class="Function">compute-sum-add-mul-nat-Semiring</a><a id="3338" class="Symbol">)</a>
</pre>
### 69. Greatest common divisor algorithm {#69}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

<pre class="Agda"><a id="3461" class="Keyword">open</a> <a id="3466" class="Keyword">import</a>
  <a id="3475" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html" class="Module">elementary-number-theory.greatest-common-divisor-natural-numbers</a> <a id="3540" class="Keyword">using</a>
  <a id="3548" class="Symbol">(</a> <a id="3550" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html#5373" class="Function">GCD-ℕ</a><a id="3555" class="Symbol">)</a>
</pre>
### 74. The principle of mathematical induction {#74}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

<pre class="Agda"><a id="3684" class="Keyword">open</a> <a id="3689" class="Keyword">import</a> <a id="3696" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a> <a id="3737" class="Keyword">using</a>
  <a id="3745" class="Symbol">(</a> <a id="3747" href="elementary-number-theory.natural-numbers.html#2052" class="Function">ind-ℕ</a><a id="3752" class="Symbol">)</a>
</pre>
### 80. The fundamental theorem of arithmetic {#80}

**Author:** [Victor Blanchi](https://github.com/VictorBlanchi)

<pre class="Agda"><a id="3884" class="Keyword">open</a> <a id="3889" class="Keyword">import</a> <a id="3896" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html" class="Module">elementary-number-theory.fundamental-theorem-of-arithmetic</a> <a id="3955" class="Keyword">using</a>
  <a id="3963" class="Symbol">(</a> <a id="3965" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html#33687" class="Function">fundamental-theorem-arithmetic-list-ℕ</a><a id="4002" class="Symbol">)</a>
</pre>
### 91. The triangle inequality {#91}

**Author:** [malarbol](https://github.com/malarbol)

<pre class="Agda"><a id="4109" class="Keyword">open</a> <a id="4114" class="Keyword">import</a> <a id="4121" href="real-numbers.metric-space-of-real-numbers.html" class="Module">real-numbers.metric-space-of-real-numbers</a> <a id="4163" class="Keyword">using</a>
  <a id="4171" class="Symbol">(</a> <a id="4173" href="real-numbers.metric-space-of-real-numbers.html#4804" class="Function">is-triangular-neighborhood-ℝ</a><a id="4201" class="Symbol">)</a>
</pre>
**Author:** [Louis Wasserman](https://github.com/lowasser)

<pre class="Agda"><a id="4276" class="Keyword">open</a> <a id="4281" class="Keyword">import</a> <a id="4288" href="real-numbers.absolute-value-real-numbers.html" class="Module">real-numbers.absolute-value-real-numbers</a> <a id="4329" class="Keyword">using</a>
  <a id="4337" class="Symbol">(</a> <a id="4339" href="real-numbers.absolute-value-real-numbers.html#3773" class="Function">triangle-inequality-abs-ℝ</a><a id="4364" class="Symbol">)</a>

<a id="4367" class="Keyword">open</a> <a id="4372" class="Keyword">import</a> <a id="4379" href="real-numbers.distance-real-numbers.html" class="Module">real-numbers.distance-real-numbers</a> <a id="4414" class="Keyword">using</a>
  <a id="4422" class="Symbol">(</a> <a id="4424" href="real-numbers.distance-real-numbers.html#5860" class="Function">triangle-inequality-dist-ℝ</a><a id="4450" class="Symbol">)</a>
</pre>
## See also

- The spiritual successor to _Formalizing 100 Theorems_ is _1000+ theorems_
  {{#cite 1000+theorems}}.

## References

{{#bibliography}}
