# The Twin Prime conjecture

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="elementary-number-theory.twin-prime-conjecture.html" class="Module">elementary-number-theory.twin-prime-conjecture</a> <a id="92" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a>
<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="elementary-number-theory.prime-numbers.html" class="Module">elementary-number-theory.prime-numbers</a>

<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="364" class="Keyword">open</a> <a id="369" class="Keyword">import</a> <a id="376" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="408" class="Keyword">open</a> <a id="413" class="Keyword">import</a> <a id="420" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Statement

The twin prime conjecture asserts that there are infinitely many twin primes. We
assert that there are infinitely twin primes by asserting that for every n : ℕ
there is a twin prime that is larger than n.

<pre class="Agda"><a id="is-twin-prime-ℕ"></a><a id="692" href="elementary-number-theory.twin-prime-conjecture.html#692" class="Function">is-twin-prime-ℕ</a> <a id="708" class="Symbol">:</a> <a id="710" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="712" class="Symbol">→</a> <a id="714" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="717" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="723" href="elementary-number-theory.twin-prime-conjecture.html#692" class="Function">is-twin-prime-ℕ</a> <a id="739" href="elementary-number-theory.twin-prime-conjecture.html#739" class="Bound">n</a> <a id="741" class="Symbol">=</a> <a id="743" class="Symbol">(</a><a id="744" href="elementary-number-theory.prime-numbers.html#1562" class="Function">is-prime-ℕ</a> <a id="755" href="elementary-number-theory.twin-prime-conjecture.html#739" class="Bound">n</a><a id="756" class="Symbol">)</a> <a id="758" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="760" class="Symbol">(</a><a id="761" href="elementary-number-theory.prime-numbers.html#1562" class="Function">is-prime-ℕ</a> <a id="772" class="Symbol">(</a><a id="773" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="780" class="Symbol">(</a><a id="781" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="788" href="elementary-number-theory.twin-prime-conjecture.html#739" class="Bound">n</a><a id="789" class="Symbol">)))</a>

<a id="twin-prime-conjecture"></a><a id="794" href="elementary-number-theory.twin-prime-conjecture.html#794" class="Function">twin-prime-conjecture</a> <a id="816" class="Symbol">:</a> <a id="818" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="821" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="827" href="elementary-number-theory.twin-prime-conjecture.html#794" class="Function">twin-prime-conjecture</a> <a id="849" class="Symbol">=</a>
  <a id="853" class="Symbol">(</a><a id="854" href="elementary-number-theory.twin-prime-conjecture.html#854" class="Bound">n</a> <a id="856" class="Symbol">:</a> <a id="858" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="859" class="Symbol">)</a> <a id="861" class="Symbol">→</a> <a id="863" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="865" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="867" class="Symbol">(λ</a> <a id="870" href="elementary-number-theory.twin-prime-conjecture.html#870" class="Bound">p</a> <a id="872" class="Symbol">→</a> <a id="874" class="Symbol">(</a><a id="875" href="elementary-number-theory.twin-prime-conjecture.html#692" class="Function">is-twin-prime-ℕ</a> <a id="891" href="elementary-number-theory.twin-prime-conjecture.html#870" class="Bound">p</a><a id="892" class="Symbol">)</a> <a id="894" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="896" class="Symbol">(</a><a id="897" href="elementary-number-theory.inequality-natural-numbers.html#1276" class="Function">leq-ℕ</a> <a id="903" href="elementary-number-theory.twin-prime-conjecture.html#854" class="Bound">n</a> <a id="905" href="elementary-number-theory.twin-prime-conjecture.html#870" class="Bound">p</a><a id="906" class="Symbol">))</a>
</pre>