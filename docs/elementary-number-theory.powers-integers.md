# Powers of integers

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="elementary-number-theory.powers-integers.html" class="Module">elementary-number-theory.powers-integers</a> <a id="79" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="135" class="Keyword">open</a> <a id="140" class="Keyword">import</a> <a id="147" href="commutative-algebra.powers-of-elements-commutative-rings.html" class="Module">commutative-algebra.powers-of-elements-commutative-rings</a>

<a id="205" class="Keyword">open</a> <a id="210" class="Keyword">import</a> <a id="217" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a>
<a id="251" class="Keyword">open</a> <a id="256" class="Keyword">import</a> <a id="263" href="elementary-number-theory.multiplication-integers.html" class="Module">elementary-number-theory.multiplication-integers</a>
<a id="312" class="Keyword">open</a> <a id="317" class="Keyword">import</a> <a id="324" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="365" class="Keyword">open</a> <a id="370" class="Keyword">import</a> <a id="377" href="elementary-number-theory.ring-of-integers.html" class="Module">elementary-number-theory.ring-of-integers</a>

<a id="420" class="Keyword">open</a> <a id="425" class="Keyword">import</a> <a id="432" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
</pre>
</details>

## Idea

The power operation on the integers is the map `n x ↦ xⁿ`, which is defined by
iteratively multiplying `x` with itself `n` times.

## Definition

<pre class="Agda"><a id="power-ℤ"></a><a id="638" href="elementary-number-theory.powers-integers.html#638" class="Function">power-ℤ</a> <a id="646" class="Symbol">:</a> <a id="648" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="650" class="Symbol">→</a> <a id="652" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a> <a id="654" class="Symbol">→</a> <a id="656" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a>
<a id="658" href="elementary-number-theory.powers-integers.html#638" class="Function">power-ℤ</a> <a id="666" class="Symbol">=</a> <a id="668" href="commutative-algebra.powers-of-elements-commutative-rings.html#784" class="Function">power-Commutative-Ring</a> <a id="691" href="elementary-number-theory.ring-of-integers.html#1471" class="Function">ℤ-Commutative-Ring</a>
</pre>
## Properties

### `xⁿ⁺¹ = xⁿx`

<pre class="Agda"><a id="power-succ-ℤ"></a><a id="756" href="elementary-number-theory.powers-integers.html#756" class="Function">power-succ-ℤ</a> <a id="769" class="Symbol">:</a> <a id="771" class="Symbol">(</a><a id="772" href="elementary-number-theory.powers-integers.html#772" class="Bound">n</a> <a id="774" class="Symbol">:</a> <a id="776" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="777" class="Symbol">)</a> <a id="779" class="Symbol">(</a><a id="780" href="elementary-number-theory.powers-integers.html#780" class="Bound">x</a> <a id="782" class="Symbol">:</a> <a id="784" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a><a id="785" class="Symbol">)</a> <a id="787" class="Symbol">→</a> <a id="789" href="elementary-number-theory.powers-integers.html#638" class="Function">power-ℤ</a> <a id="797" class="Symbol">(</a><a id="798" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="805" href="elementary-number-theory.powers-integers.html#772" class="Bound">n</a><a id="806" class="Symbol">)</a> <a id="808" href="elementary-number-theory.powers-integers.html#780" class="Bound">x</a> <a id="810" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="812" class="Symbol">(</a><a id="813" href="elementary-number-theory.powers-integers.html#638" class="Function">power-ℤ</a> <a id="821" href="elementary-number-theory.powers-integers.html#772" class="Bound">n</a> <a id="823" href="elementary-number-theory.powers-integers.html#780" class="Bound">x</a><a id="824" class="Symbol">)</a> <a id="826" href="elementary-number-theory.multiplication-integers.html#1978" class="Function Operator">*ℤ</a> <a id="829" href="elementary-number-theory.powers-integers.html#780" class="Bound">x</a>
<a id="831" href="elementary-number-theory.powers-integers.html#756" class="Function">power-succ-ℤ</a> <a id="844" class="Symbol">=</a> <a id="846" href="commutative-algebra.powers-of-elements-commutative-rings.html#1092" class="Function">power-succ-Commutative-Ring</a> <a id="874" href="elementary-number-theory.ring-of-integers.html#1471" class="Function">ℤ-Commutative-Ring</a>
</pre>