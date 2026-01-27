# Catalan numbers

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="elementary-number-theory.catalan-numbers.html" class="Module">elementary-number-theory.catalan-numbers</a> <a id="76" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="132" class="Keyword">open</a> <a id="137" class="Keyword">import</a> <a id="144" href="elementary-number-theory.binomial-coefficients.html" class="Module">elementary-number-theory.binomial-coefficients</a>
<a id="191" class="Keyword">open</a> <a id="196" class="Keyword">import</a> <a id="203" href="elementary-number-theory.distance-natural-numbers.html" class="Module">elementary-number-theory.distance-natural-numbers</a>
<a id="253" class="Keyword">open</a> <a id="258" class="Keyword">import</a> <a id="265" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a>
<a id="321" class="Keyword">open</a> <a id="326" class="Keyword">import</a> <a id="333" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="374" class="Keyword">open</a> <a id="379" class="Keyword">import</a> <a id="386" href="elementary-number-theory.strict-inequality-natural-numbers.html" class="Module">elementary-number-theory.strict-inequality-natural-numbers</a>
<a id="445" class="Keyword">open</a> <a id="450" class="Keyword">import</a> <a id="457" href="elementary-number-theory.strong-induction-natural-numbers.html" class="Module">elementary-number-theory.strong-induction-natural-numbers</a>
<a id="515" class="Keyword">open</a> <a id="520" class="Keyword">import</a> <a id="527" href="elementary-number-theory.sums-of-natural-numbers.html" class="Module">elementary-number-theory.sums-of-natural-numbers</a>

<a id="577" class="Keyword">open</a> <a id="582" class="Keyword">import</a> <a id="589" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

The
{{#concept "Catalan numbers" WD="Catalan number" WDID=Q270513 OEIS=A000108 Agda=catalan-numbers}}
$C_n$ is a [sequence](lists.sequences.md) of
[natural numbers](elementary-number-theory.natural-numbers.md) that occur in
several combinatorics problems. The sequence starts

```text
  n   0   1   2   3   4   5   6
  Cₙ  1   1   2   5  14  42 132 ⋯
```

The Catalan numbers may be defined by any of the formulas

1. $C_{n + 1} = \sum_{k = 0}^n C_k C_{n-k}$, with $C_0 = 1$,
2. $C_n = {2n \choose n} - {2n \choose n + 1}$,
3. $C_{n+1} = \frac{2(2n+1)}{n+2}C_n$, with $C_0 = 1$,
4. $C_{n} = \frac{1}{n+1}{2n \choose n}$,
5. $C_{n} = \frac{(2n)!}{(n+1)!n!}$.

Where $n \choose k$ are
[binomial coefficients](elementary-number-theory.binomial-coefficients.md) and
$n!$ is the [factorial function](elementary-number-theory.factorials.md).

## Definitions

### Inductive sum formula for the Catalan numbers

The Catalan numbers may be defined to be the sequence satisfying $C_0 = 1$ and
the recurrence relation

$$
C_{n + 1} = \sum_{k = 0}^n C_k C_{n-k}.
$$

<pre class="Agda"><a id="catalan-numbers"></a><a id="1724" href="elementary-number-theory.catalan-numbers.html#1724" class="Function">catalan-numbers</a> <a id="1740" class="Symbol">:</a> <a id="1742" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1744" class="Symbol">→</a> <a id="1746" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1748" href="elementary-number-theory.catalan-numbers.html#1724" class="Function">catalan-numbers</a> <a id="1764" class="Symbol">=</a>
  <a id="1768" href="elementary-number-theory.strong-induction-natural-numbers.html#4552" class="Function">strong-ind-ℕ</a>
    <a id="1785" class="Symbol">(</a> <a id="1787" class="Symbol">λ</a> <a id="1789" href="elementary-number-theory.catalan-numbers.html#1789" class="Bound">_</a> <a id="1791" class="Symbol">→</a> <a id="1793" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1794" class="Symbol">)</a>
    <a id="1800" class="Symbol">(</a> <a id="1802" class="Number">1</a><a id="1803" class="Symbol">)</a>
    <a id="1809" class="Symbol">(</a> <a id="1811" class="Symbol">λ</a> <a id="1813" href="elementary-number-theory.catalan-numbers.html#1813" class="Bound">k</a> <a id="1815" href="elementary-number-theory.catalan-numbers.html#1815" class="Bound">C</a> <a id="1817" class="Symbol">→</a>
      <a id="1825" href="elementary-number-theory.sums-of-natural-numbers.html#1280" class="Function">sum-Fin-ℕ</a> <a id="1835" href="elementary-number-theory.catalan-numbers.html#1813" class="Bound">k</a>
        <a id="1845" class="Symbol">(</a> <a id="1847" class="Symbol">λ</a> <a id="1849" href="elementary-number-theory.catalan-numbers.html#1849" class="Bound">i</a> <a id="1851" class="Symbol">→</a>
          <a id="1863" href="elementary-number-theory.multiplication-natural-numbers.html#1312" class="Function">mul-ℕ</a>
            <a id="1881" class="Symbol">(</a> <a id="1883" href="elementary-number-theory.catalan-numbers.html#1815" class="Bound">C</a> <a id="1885" class="Symbol">(</a> <a id="1887" href="univalent-combinatorics.standard-finite-types.html#6914" class="Function">nat-Fin</a> <a id="1895" href="elementary-number-theory.catalan-numbers.html#1813" class="Bound">k</a> <a id="1897" href="elementary-number-theory.catalan-numbers.html#1849" class="Bound">i</a><a id="1898" class="Symbol">)</a>
                <a id="1916" class="Symbol">(</a> <a id="1918" href="elementary-number-theory.strict-inequality-natural-numbers.html#8525" class="Function">leq-le-ℕ</a> <a id="1927" class="Symbol">(</a><a id="1928" href="univalent-combinatorics.standard-finite-types.html#6914" class="Function">nat-Fin</a> <a id="1936" href="elementary-number-theory.catalan-numbers.html#1813" class="Bound">k</a> <a id="1938" href="elementary-number-theory.catalan-numbers.html#1849" class="Bound">i</a><a id="1939" class="Symbol">)</a> <a id="1941" href="elementary-number-theory.catalan-numbers.html#1813" class="Bound">k</a> <a id="1943" class="Symbol">(</a><a id="1944" href="univalent-combinatorics.standard-finite-types.html#7161" class="Function">strict-upper-bound-nat-Fin</a> <a id="1971" href="elementary-number-theory.catalan-numbers.html#1813" class="Bound">k</a> <a id="1973" href="elementary-number-theory.catalan-numbers.html#1849" class="Bound">i</a><a id="1974" class="Symbol">)))</a>
            <a id="1990" class="Symbol">(</a> <a id="1992" href="elementary-number-theory.catalan-numbers.html#1815" class="Bound">C</a> <a id="1994" class="Symbol">(</a> <a id="1996" href="elementary-number-theory.distance-natural-numbers.html#1461" class="Function">dist-ℕ</a> <a id="2003" class="Symbol">(</a><a id="2004" href="univalent-combinatorics.standard-finite-types.html#6914" class="Function">nat-Fin</a> <a id="2012" href="elementary-number-theory.catalan-numbers.html#1813" class="Bound">k</a> <a id="2014" href="elementary-number-theory.catalan-numbers.html#1849" class="Bound">i</a><a id="2015" class="Symbol">)</a> <a id="2017" href="elementary-number-theory.catalan-numbers.html#1813" class="Bound">k</a><a id="2018" class="Symbol">)</a>
                <a id="2036" class="Symbol">(</a> <a id="2038" href="elementary-number-theory.distance-natural-numbers.html#9797" class="Function">leq-dist-ℕ</a>
                  <a id="2067" class="Symbol">(</a> <a id="2069" href="univalent-combinatorics.standard-finite-types.html#6914" class="Function">nat-Fin</a> <a id="2077" href="elementary-number-theory.catalan-numbers.html#1813" class="Bound">k</a> <a id="2079" href="elementary-number-theory.catalan-numbers.html#1849" class="Bound">i</a><a id="2080" class="Symbol">)</a>
                  <a id="2100" class="Symbol">(</a> <a id="2102" href="elementary-number-theory.catalan-numbers.html#1813" class="Bound">k</a><a id="2103" class="Symbol">)</a>
                  <a id="2123" class="Symbol">(</a> <a id="2125" href="elementary-number-theory.strict-inequality-natural-numbers.html#8525" class="Function">leq-le-ℕ</a>
                    <a id="2154" class="Symbol">(</a> <a id="2156" href="univalent-combinatorics.standard-finite-types.html#6914" class="Function">nat-Fin</a> <a id="2164" href="elementary-number-theory.catalan-numbers.html#1813" class="Bound">k</a> <a id="2166" href="elementary-number-theory.catalan-numbers.html#1849" class="Bound">i</a><a id="2167" class="Symbol">)</a>
                    <a id="2189" class="Symbol">(</a> <a id="2191" href="elementary-number-theory.catalan-numbers.html#1813" class="Bound">k</a><a id="2192" class="Symbol">)</a>
                    <a id="2214" class="Symbol">(</a> <a id="2216" href="univalent-combinatorics.standard-finite-types.html#7161" class="Function">strict-upper-bound-nat-Fin</a> <a id="2243" href="elementary-number-theory.catalan-numbers.html#1813" class="Bound">k</a> <a id="2245" href="elementary-number-theory.catalan-numbers.html#1849" class="Bound">i</a><a id="2246" class="Symbol">))))))</a>
</pre>
### Binomial difference formula for the Catalan numbers

The Catalan numbers may be computed as a
[distance](elementary-number-theory.distance-natural-numbers.md) between two
consecutive binomial coefficients

$$
C_n = \lvert{2n \choose n} - {2n \choose n + 1}\rvert.
$$

Since ${2n \choose n}$ in general is larger than or equal to
${2n \choose n + 1}$, this distance is equal to the difference

$$
C_n = {2n \choose n} - {2n \choose n + 1}.
$$

However, we prefer the use of the distance binary operation on natural numbers
in general at it is a total function on natural numbers, and allows us to skip
proving this inequality.

<pre class="Agda"><a id="catalan-numbers-binomial"></a><a id="2897" href="elementary-number-theory.catalan-numbers.html#2897" class="Function">catalan-numbers-binomial</a> <a id="2922" class="Symbol">:</a> <a id="2924" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2926" class="Symbol">→</a> <a id="2928" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="2930" href="elementary-number-theory.catalan-numbers.html#2897" class="Function">catalan-numbers-binomial</a> <a id="2955" href="elementary-number-theory.catalan-numbers.html#2955" class="Bound">n</a> <a id="2957" class="Symbol">=</a>
  <a id="2961" href="elementary-number-theory.distance-natural-numbers.html#1461" class="Function">dist-ℕ</a>
    <a id="2972" class="Symbol">(</a> <a id="2974" href="elementary-number-theory.binomial-coefficients.html#1394" class="Function">binomial-coefficient-ℕ</a> <a id="2997" class="Symbol">(</a><a id="2998" class="Number">2</a> <a id="3000" href="elementary-number-theory.multiplication-natural-numbers.html#1398" class="Primitive Operator">*ℕ</a> <a id="3003" href="elementary-number-theory.catalan-numbers.html#2955" class="Bound">n</a><a id="3004" class="Symbol">)</a> <a id="3006" href="elementary-number-theory.catalan-numbers.html#2955" class="Bound">n</a><a id="3007" class="Symbol">)</a>
    <a id="3013" class="Symbol">(</a> <a id="3015" href="elementary-number-theory.binomial-coefficients.html#1394" class="Function">binomial-coefficient-ℕ</a> <a id="3038" class="Symbol">(</a><a id="3039" class="Number">2</a> <a id="3041" href="elementary-number-theory.multiplication-natural-numbers.html#1398" class="Primitive Operator">*ℕ</a> <a id="3044" href="elementary-number-theory.catalan-numbers.html#2955" class="Bound">n</a><a id="3045" class="Symbol">)</a> <a id="3047" class="Symbol">(</a><a id="3048" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="3055" href="elementary-number-theory.catalan-numbers.html#2955" class="Bound">n</a><a id="3056" class="Symbol">))</a>
</pre>
## External links

- [Catalan number](https://en.wikipedia.org/wiki/Catalan_number) at Wikipedia
- [Catalan Number](https://mathworld.wolfram.com/CatalanNumber.html) at Wolfram
  MathWorld
- [A000108](https://oeis.org/A000108) in the OEIS
