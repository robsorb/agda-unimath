# Fermat numbers

<pre class="Agda"><a id="27" class="Keyword">module</a> <a id="34" href="elementary-number-theory.fermat-numbers.html" class="Module">elementary-number-theory.fermat-numbers</a> <a id="74" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="130" class="Keyword">open</a> <a id="135" class="Keyword">import</a> <a id="142" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a>
<a id="192" class="Keyword">open</a> <a id="197" class="Keyword">import</a> <a id="204" href="elementary-number-theory.exponentiation-natural-numbers.html" class="Module">elementary-number-theory.exponentiation-natural-numbers</a>
<a id="260" class="Keyword">open</a> <a id="265" class="Keyword">import</a> <a id="272" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="313" class="Keyword">open</a> <a id="318" class="Keyword">import</a> <a id="325" href="elementary-number-theory.products-of-natural-numbers.html" class="Module">elementary-number-theory.products-of-natural-numbers</a>
<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="elementary-number-theory.strong-induction-natural-numbers.html" class="Module">elementary-number-theory.strong-induction-natural-numbers</a>

<a id="449" class="Keyword">open</a> <a id="454" class="Keyword">import</a> <a id="461" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

{{#concept "Fermat numbers" WD="Fermat number" WDID=Q207264 Agda=fermat-number-ℕ}}
are numbers of the form $F_n := 2^{2^n}+1$. The first five Fermat numbers are

```text
  3, 5, 17, 257, and 65537.
```

The sequence of Fermat numbers is listed as A000215 in the
[Online Encyclopedia of Integer Sequences](literature.oeis.md).

Alternatively, the Fermat numbers can be defined with
[strong induction](elementary-number-theory.strong-induction-natural-numbers.md)
by

```text
F 0 := 3
F (n + 1) := 2 + Π_{i≤n} F_i
```

This recurrence implies that any two Fermat numbers are
[relatively prime](elementary-number-theory.relatively-prime-natural-numbers.md).
Goldbach used this observation to prove the
[infinitude of primes](elementary-number-theory.infinitude-of-primes.md): Since
there are infinitely many Fermat numbers, and all of them are relatively prime,
there must be infinitely many prime numbers. Fermat numbers also feature in a
series of long-standing open problems in mathematics, including:

- Are there infinitely many prime Fermat numbers?
- Is $F_n$ composite for all $n\geq 5$?

## Definition

### The Fermat numbers

<pre class="Agda"><a id="fermat-number-ℕ"></a><a id="1674" href="elementary-number-theory.fermat-numbers.html#1674" class="Function">fermat-number-ℕ</a> <a id="1690" class="Symbol">:</a> <a id="1692" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1694" class="Symbol">→</a> <a id="1696" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1698" href="elementary-number-theory.fermat-numbers.html#1674" class="Function">fermat-number-ℕ</a> <a id="1714" href="elementary-number-theory.fermat-numbers.html#1714" class="Bound">n</a> <a id="1716" class="Symbol">=</a> <a id="1718" href="elementary-number-theory.exponentiation-natural-numbers.html#927" class="Function">exp-ℕ</a> <a id="1724" class="Number">2</a> <a id="1726" class="Symbol">(</a><a id="1727" href="elementary-number-theory.exponentiation-natural-numbers.html#927" class="Function">exp-ℕ</a> <a id="1733" class="Number">2</a> <a id="1735" href="elementary-number-theory.fermat-numbers.html#1714" class="Bound">n</a><a id="1736" class="Symbol">)</a> <a id="1738" href="elementary-number-theory.addition-natural-numbers.html#907" class="Primitive Operator">+ℕ</a> <a id="1741" class="Number">1</a>
</pre>
### The recursive definition of the Fermat numbers

<pre class="Agda"><a id="recursive-fermat-number-ℕ"></a><a id="1808" href="elementary-number-theory.fermat-numbers.html#1808" class="Function">recursive-fermat-number-ℕ</a> <a id="1834" class="Symbol">:</a> <a id="1836" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1838" class="Symbol">→</a> <a id="1840" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1842" href="elementary-number-theory.fermat-numbers.html#1808" class="Function">recursive-fermat-number-ℕ</a> <a id="1868" class="Symbol">=</a>
  <a id="1872" href="elementary-number-theory.strong-induction-natural-numbers.html#8010" class="Function">strong-rec-ℕ</a> <a id="1885" class="Number">3</a>
    <a id="1891" class="Symbol">(</a> <a id="1893" class="Symbol">λ</a> <a id="1895" href="elementary-number-theory.fermat-numbers.html#1895" class="Bound">n</a> <a id="1897" href="elementary-number-theory.fermat-numbers.html#1897" class="Bound">f</a> <a id="1899" class="Symbol">→</a>
      <a id="1907" href="elementary-number-theory.addition-natural-numbers.html#819" class="Function">add-ℕ</a>
        <a id="1921" class="Symbol">(</a> <a id="1923" href="elementary-number-theory.products-of-natural-numbers.html#908" class="Function">Π-ℕ</a>
          <a id="1937" class="Symbol">(</a> <a id="1939" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1946" href="elementary-number-theory.fermat-numbers.html#1895" class="Bound">n</a><a id="1947" class="Symbol">)</a>
          <a id="1959" class="Symbol">(</a> <a id="1961" class="Symbol">λ</a> <a id="1963" href="elementary-number-theory.fermat-numbers.html#1963" class="Bound">i</a> <a id="1965" class="Symbol">→</a> <a id="1967" href="elementary-number-theory.fermat-numbers.html#1897" class="Bound">f</a> <a id="1969" class="Symbol">(</a><a id="1970" href="univalent-combinatorics.standard-finite-types.html#6914" class="Function">nat-Fin</a> <a id="1978" class="Symbol">(</a><a id="1979" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1986" href="elementary-number-theory.fermat-numbers.html#1895" class="Bound">n</a><a id="1987" class="Symbol">)</a> <a id="1989" href="elementary-number-theory.fermat-numbers.html#1963" class="Bound">i</a><a id="1990" class="Symbol">)</a> <a id="1992" class="Symbol">(</a><a id="1993" href="univalent-combinatorics.standard-finite-types.html#7466" class="Function">upper-bound-nat-Fin</a> <a id="2013" href="elementary-number-theory.fermat-numbers.html#1895" class="Bound">n</a> <a id="2015" href="elementary-number-theory.fermat-numbers.html#1963" class="Bound">i</a><a id="2016" class="Symbol">)))</a>
        <a id="2028" class="Symbol">(</a> <a id="2030" class="Number">2</a><a id="2031" class="Symbol">))</a>
</pre>
## External link

- [Fermat number](https://en.wikipedia.org/wiki/Fermat_number) at Wikipedia
- [A000215](https://oeis.org/A000215) in the OEIS
