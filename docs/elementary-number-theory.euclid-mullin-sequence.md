# The Euclid–Mullin sequence

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="elementary-number-theory.euclid-mullin-sequence.html" class="Module">elementary-number-theory.euclid-mullin-sequence</a> <a id="94" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="150" class="Keyword">open</a> <a id="155" class="Keyword">import</a> <a id="162" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html" class="Module">elementary-number-theory.fundamental-theorem-of-arithmetic</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="274" class="Keyword">open</a> <a id="279" class="Keyword">import</a> <a id="286" href="elementary-number-theory.products-of-natural-numbers.html" class="Module">elementary-number-theory.products-of-natural-numbers</a>
<a id="339" class="Keyword">open</a> <a id="344" class="Keyword">import</a> <a id="351" href="elementary-number-theory.strict-inequality-natural-numbers.html" class="Module">elementary-number-theory.strict-inequality-natural-numbers</a>
<a id="410" class="Keyword">open</a> <a id="415" class="Keyword">import</a> <a id="422" href="elementary-number-theory.strong-induction-natural-numbers.html" class="Module">elementary-number-theory.strong-induction-natural-numbers</a>

<a id="481" class="Keyword">open</a> <a id="486" class="Keyword">import</a> <a id="493" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="525" class="Keyword">open</a> <a id="530" class="Keyword">import</a> <a id="537" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="563" class="Keyword">open</a> <a id="568" class="Keyword">import</a> <a id="575" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>

<a id="597" class="Keyword">open</a> <a id="602" class="Keyword">import</a> <a id="609" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

The
{{#concept "Euclid–Mullin sequence" Agda=euclid-mullin-ℕ WDID=Q5406148 WD="Euclid-Mullin sequence"}}
is a [sequence](lists.sequences.md) of
[natural numbers](elementary-number-theory.natural-numbers.md), which is defined
by
[strong induction](elementary-number-theory.strong-induction-natural-numbers.md)
by

```text
  euclid-mullin-ℕ 0 := 2,
```

and `euclid-mullin-ℕ (n + 1)` is the least
[prime factor](elementary-number-theory.prime-numbers.md) of the product of all
previous entries in the Euclid–Mullin sequence plus one.

## Definitions

### The Euclid–Mullin sequence

<pre class="Agda"><a id="euclid-mullin-ℕ"></a><a id="1270" href="elementary-number-theory.euclid-mullin-sequence.html#1270" class="Function">euclid-mullin-ℕ</a> <a id="1286" class="Symbol">:</a> <a id="1288" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1290" class="Symbol">→</a> <a id="1292" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1294" href="elementary-number-theory.euclid-mullin-sequence.html#1270" class="Function">euclid-mullin-ℕ</a> <a id="1310" class="Symbol">=</a>
  <a id="1314" href="elementary-number-theory.strong-induction-natural-numbers.html#8010" class="Function">strong-rec-ℕ</a>
    <a id="1331" class="Symbol">(</a> <a id="1333" class="Number">2</a><a id="1334" class="Symbol">)</a>
    <a id="1340" class="Symbol">(</a> <a id="1342" class="Symbol">λ</a> <a id="1344" href="elementary-number-theory.euclid-mullin-sequence.html#1344" class="Bound">n</a> <a id="1346" href="elementary-number-theory.euclid-mullin-sequence.html#1346" class="Bound">f</a> <a id="1348" class="Symbol">→</a>
      <a id="1356" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html#10689" class="Function">nat-least-nontrivial-divisor-ℕ&#39;</a>
        <a id="1396" class="Symbol">(</a> <a id="1398" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a>
          <a id="1415" class="Symbol">(</a> <a id="1417" href="elementary-number-theory.products-of-natural-numbers.html#908" class="Function">Π-ℕ</a>
            <a id="1433" class="Symbol">(</a> <a id="1435" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1442" href="elementary-number-theory.euclid-mullin-sequence.html#1344" class="Bound">n</a><a id="1443" class="Symbol">)</a>
            <a id="1457" class="Symbol">(</a> <a id="1459" class="Symbol">λ</a> <a id="1461" href="elementary-number-theory.euclid-mullin-sequence.html#1461" class="Bound">i</a> <a id="1463" class="Symbol">→</a> <a id="1465" href="elementary-number-theory.euclid-mullin-sequence.html#1346" class="Bound">f</a> <a id="1467" class="Symbol">(</a><a id="1468" href="univalent-combinatorics.standard-finite-types.html#6914" class="Function">nat-Fin</a> <a id="1476" class="Symbol">(</a><a id="1477" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1484" href="elementary-number-theory.euclid-mullin-sequence.html#1344" class="Bound">n</a><a id="1485" class="Symbol">)</a> <a id="1487" href="elementary-number-theory.euclid-mullin-sequence.html#1461" class="Bound">i</a><a id="1488" class="Symbol">)</a> <a id="1490" class="Symbol">(</a><a id="1491" href="univalent-combinatorics.standard-finite-types.html#7466" class="Function">upper-bound-nat-Fin</a> <a id="1511" href="elementary-number-theory.euclid-mullin-sequence.html#1344" class="Bound">n</a> <a id="1513" href="elementary-number-theory.euclid-mullin-sequence.html#1461" class="Bound">i</a><a id="1514" class="Symbol">)))))</a>

<a id="compute-euclid-mullin-0-ℕ"></a><a id="1521" href="elementary-number-theory.euclid-mullin-sequence.html#1521" class="Function">compute-euclid-mullin-0-ℕ</a> <a id="1547" class="Symbol">:</a> <a id="1549" href="elementary-number-theory.euclid-mullin-sequence.html#1270" class="Function">euclid-mullin-ℕ</a> <a id="1565" class="Number">0</a> <a id="1567" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1569" class="Number">2</a>
<a id="1571" href="elementary-number-theory.euclid-mullin-sequence.html#1521" class="Function">compute-euclid-mullin-0-ℕ</a> <a id="1597" class="Symbol">=</a> <a id="1599" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="compute-euclid-mullin-1-ℕ"></a><a id="1605" href="elementary-number-theory.euclid-mullin-sequence.html#1605" class="Function">compute-euclid-mullin-1-ℕ</a> <a id="1631" class="Symbol">:</a> <a id="1633" href="elementary-number-theory.euclid-mullin-sequence.html#1270" class="Function">euclid-mullin-ℕ</a> <a id="1649" class="Number">1</a> <a id="1651" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1653" class="Number">3</a>
<a id="1655" href="elementary-number-theory.euclid-mullin-sequence.html#1605" class="Function">compute-euclid-mullin-1-ℕ</a> <a id="1681" class="Symbol">=</a> <a id="1683" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="compute-euclid-mullin-2-ℕ"></a><a id="1689" href="elementary-number-theory.euclid-mullin-sequence.html#1689" class="Function">compute-euclid-mullin-2-ℕ</a> <a id="1715" class="Symbol">:</a> <a id="1717" href="elementary-number-theory.euclid-mullin-sequence.html#1270" class="Function">euclid-mullin-ℕ</a> <a id="1733" class="Number">2</a> <a id="1735" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1737" class="Number">7</a>
<a id="1739" href="elementary-number-theory.euclid-mullin-sequence.html#1689" class="Function">compute-euclid-mullin-2-ℕ</a> <a id="1765" class="Symbol">=</a> <a id="1767" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
The following computations also type-check, but take a very long time to
terminate.

```text
compute-euclid-mullin-3-ℕ : euclid-mullin-ℕ 3 ＝ 43
compute-euclid-mullin-3-ℕ = refl

compute-euclid-mullin-4-ℕ : euclid-mullin-ℕ 4 ＝ 13
compute-euclid-mullin-4-ℕ = refl

compute-euclid-mullin-5-ℕ : euclid-mullin-ℕ 5 ＝ 53
compute-euclid-mullin-5-ℕ = refl

compute-euclid-mullin-6-ℕ : euclid-mullin-ℕ 6 ＝ 5
compute-euclid-mullin-6-ℕ = refl

compute-euclid-mullin-7-ℕ : euclid-mullin-ℕ 7 ＝ 6221671
compute-euclid-mullin-7-ℕ = refl

compute-euclid-mullin-8-ℕ : euclid-mullin-ℕ 8 ＝ 38709183810571
compute-euclid-mullin-8-ℕ = refl
```
