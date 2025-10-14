# The Jacobi symbol

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="elementary-number-theory.jacobi-symbol.html" class="Module">elementary-number-theory.jacobi-symbol</a> <a id="76" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="132" class="Keyword">open</a> <a id="137" class="Keyword">import</a> <a id="144" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html" class="Module">elementary-number-theory.fundamental-theorem-of-arithmetic</a>
<a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a>
<a id="249" class="Keyword">open</a> <a id="254" class="Keyword">import</a> <a id="261" href="elementary-number-theory.legendre-symbol.html" class="Module">elementary-number-theory.legendre-symbol</a>
<a id="302" class="Keyword">open</a> <a id="307" class="Keyword">import</a> <a id="314" href="elementary-number-theory.multiplication-integers.html" class="Module">elementary-number-theory.multiplication-integers</a>
<a id="363" class="Keyword">open</a> <a id="368" class="Keyword">import</a> <a id="375" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="417" class="Keyword">open</a> <a id="422" class="Keyword">import</a> <a id="429" href="foundation.type-arithmetic-dependent-function-types.html" class="Module">foundation.type-arithmetic-dependent-function-types</a>
<a id="481" class="Keyword">open</a> <a id="486" class="Keyword">import</a> <a id="493" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>

<a id="515" class="Keyword">open</a> <a id="520" class="Keyword">import</a> <a id="527" href="lists.functoriality-lists.html" class="Module">lists.functoriality-lists</a>
<a id="553" class="Keyword">open</a> <a id="558" class="Keyword">import</a> <a id="565" href="lists.lists.html" class="Module">lists.lists</a>
</pre>
</details>

## Idea

The
{{#concept "Jacobi symbol" WD="Jacobi symbol" WDID=Q241015 Agda=jacobi-symbol}}
is a function which encodes information about the
[squareness](elementary-number-theory.squares-modular-arithmetic.md) of an
[integer](elementary-number-theory.integers.md) within certain
[rings of integers modulo `p`](elementary-number-theory.modular-arithmetic.md),
for [prime](elementary-number-theory.prime-numbers.md) `p`. Specifically,
`jacobi-symbol(a,n)` for an integer `a : ℤ` and natural number `n : ℕ` is the
product of the [legendre symbols](elementary-number-theory.legendre-symbol.md)

```text
  legendre-symbol(p₁,a) · legendre-symbol(p₂,a) · … · legendre-symbol(pₖ,a),
```

where `p₁, …, pₖ` are the prime factors of `n`, not necessarily distinct (i.e.
it is possible that `pᵢ = pⱼ`).

## Definition

<pre class="Agda"><a id="jacobi-symbol"></a><a id="1412" href="elementary-number-theory.jacobi-symbol.html#1412" class="Function">jacobi-symbol</a> <a id="1426" class="Symbol">:</a> <a id="1428" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a> <a id="1430" class="Symbol">→</a> <a id="1432" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1434" class="Symbol">→</a> <a id="1436" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a>
<a id="1438" href="elementary-number-theory.jacobi-symbol.html#1412" class="Function">jacobi-symbol</a> <a id="1452" href="elementary-number-theory.jacobi-symbol.html#1452" class="Bound">a</a> <a id="1454" class="Number">0</a> <a id="1456" class="Symbol">=</a> <a id="1458" href="elementary-number-theory.integers.html#1569" class="Function">zero-ℤ</a>
<a id="1465" href="elementary-number-theory.jacobi-symbol.html#1412" class="Function">jacobi-symbol</a> <a id="1479" href="elementary-number-theory.jacobi-symbol.html#1479" class="Bound">a</a> <a id="1481" class="Number">1</a> <a id="1483" class="Symbol">=</a> <a id="1485" href="elementary-number-theory.integers.html#1852" class="Function">one-ℤ</a>
<a id="1491" href="elementary-number-theory.jacobi-symbol.html#1412" class="Function">jacobi-symbol</a> <a id="1505" href="elementary-number-theory.jacobi-symbol.html#1505" class="Bound">a</a> <a id="1507" class="Symbol">(</a><a id="1508" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1515" class="Symbol">(</a><a id="1516" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1523" href="elementary-number-theory.jacobi-symbol.html#1523" class="Bound">n</a><a id="1524" class="Symbol">))</a> <a id="1527" class="Symbol">=</a>
  <a id="1531" href="lists.lists.html#2158" class="Function">fold-list</a>
    <a id="1545" class="Symbol">(</a> <a id="1547" href="elementary-number-theory.integers.html#1852" class="Function">one-ℤ</a><a id="1552" class="Symbol">)</a>
    <a id="1558" class="Symbol">(</a> <a id="1560" href="elementary-number-theory.multiplication-integers.html#1728" class="Function">mul-ℤ</a><a id="1565" class="Symbol">)</a>
    <a id="1571" class="Symbol">(</a> <a id="1573" href="lists.functoriality-lists.html#934" class="Function">map-list</a>
      <a id="1588" class="Symbol">(</a> <a id="1590" href="foundation.type-arithmetic-dependent-function-types.html#1233" class="Function">swap-Π</a> <a id="1597" href="elementary-number-theory.legendre-symbol.html#1812" class="Function">legendre-symbol</a> <a id="1613" href="elementary-number-theory.jacobi-symbol.html#1505" class="Bound">a</a><a id="1614" class="Symbol">)</a>
      <a id="1622" class="Symbol">(</a> <a id="1624" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html#14419" class="Function">list-primes-fundamental-theorem-arithmetic-ℕ</a> <a id="1669" class="Symbol">(</a><a id="1670" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1677" class="Symbol">(</a><a id="1678" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1685" href="elementary-number-theory.jacobi-symbol.html#1523" class="Bound">n</a><a id="1686" class="Symbol">))</a> <a id="1689" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a><a id="1693" class="Symbol">))</a>
</pre>