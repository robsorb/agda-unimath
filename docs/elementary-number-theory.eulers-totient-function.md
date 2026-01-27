# Euler's totient function

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="elementary-number-theory.eulers-totient-function.html" class="Module">elementary-number-theory.eulers-totient-function</a> <a id="93" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="149" class="Keyword">open</a> <a id="154" class="Keyword">import</a> <a id="161" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="202" class="Keyword">open</a> <a id="207" class="Keyword">import</a> <a id="214" href="elementary-number-theory.relatively-prime-natural-numbers.html" class="Module">elementary-number-theory.relatively-prime-natural-numbers</a>

<a id="273" class="Keyword">open</a> <a id="278" class="Keyword">import</a> <a id="285" href="univalent-combinatorics.decidable-subtypes.html" class="Module">univalent-combinatorics.decidable-subtypes</a>
<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="377" class="Keyword">open</a> <a id="382" class="Keyword">import</a> <a id="389" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

{{#concept "Euler's totient function" WD="Euler's totient function" WDID=Q190026 Agda=eulers-totient-function-relatively-prime}}
`φ : ℕ → ℕ` is the function that maps a
[natural number](elementary-number-theory.natural-numbers.md) `n` to the number
of
[multiplicative units modulo `n`](elementary-number-theory.multiplicative-units-standard-cyclic-rings.md).
In other words, the number `φ n` is the cardinality of the
[group of units](ring-theory.groups-of-units-rings.md) of the
[ring](ring-theory.rings.md) `ℤ-Mod n`.

Alternatively, Euler's totient function can be defined as the function `ℕ → ℕ`
that returns for each `n` the number of `x < n` that are
[relatively prime](elementary-number-theory.relatively-prime-natural-numbers.md).
These two definitions of Euler's totient function agree on the _positive_
natural numbers. However, there are two multiplicative units in the
[ring `ℤ`](elementary-number-theory.ring-of-integers.md) of
[integers](elementary-number-theory.integers.md), while there are no natural
numbers `x < 0` that are relatively prime to `0`.

Our reason for preferring the first definition over the second definition is
that the usual properties of Euler's totient function, such as multiplicativity,
extend naturally to the first definition.

## Definitions

### The definition of Euler's totient function using relatively prime natural numbers

<pre class="Agda"><a id="eulers-totient-function-relatively-prime"></a><a id="1842" href="elementary-number-theory.eulers-totient-function.html#1842" class="Function">eulers-totient-function-relatively-prime</a> <a id="1883" class="Symbol">:</a> <a id="1885" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1887" class="Symbol">→</a> <a id="1889" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1891" href="elementary-number-theory.eulers-totient-function.html#1842" class="Function">eulers-totient-function-relatively-prime</a> <a id="1932" href="elementary-number-theory.eulers-totient-function.html#1932" class="Bound">n</a> <a id="1934" class="Symbol">=</a>
  <a id="1938" href="univalent-combinatorics.decidable-subtypes.html#6982" class="Function">number-of-elements-subset-Finite-Type</a>
    <a id="1980" class="Symbol">(</a> <a id="1982" href="univalent-combinatorics.finite-types.html#7711" class="Function">Fin-Finite-Type</a> <a id="1998" href="elementary-number-theory.eulers-totient-function.html#1932" class="Bound">n</a><a id="1999" class="Symbol">)</a>
    <a id="2005" class="Symbol">(</a> <a id="2007" class="Symbol">λ</a> <a id="2009" href="elementary-number-theory.eulers-totient-function.html#2009" class="Bound">x</a> <a id="2011" class="Symbol">→</a> <a id="2013" href="elementary-number-theory.relatively-prime-natural-numbers.html#2025" class="Function">is-relatively-prime-ℕ-Decidable-Prop</a> <a id="2050" class="Symbol">(</a><a id="2051" href="univalent-combinatorics.standard-finite-types.html#6914" class="Function">nat-Fin</a> <a id="2059" href="elementary-number-theory.eulers-totient-function.html#1932" class="Bound">n</a> <a id="2061" href="elementary-number-theory.eulers-totient-function.html#2009" class="Bound">x</a><a id="2062" class="Symbol">)</a> <a id="2064" href="elementary-number-theory.eulers-totient-function.html#1932" class="Bound">n</a><a id="2065" class="Symbol">)</a>
</pre>
## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}

## External links

- [Euler's totient function](https://en.wikipedia.org/wiki/Euler%27s_totient_function)
  at Wikipedia
- [Totient Function](https://mathworld.wolfram.com/TotientFunction.html) at
  Wolfram MathWorld
